/*
** $Id: ldo.c,v 2.151 2015/12/16 16:40:07 roberto Exp $
** Stack and Call structure of Lua
** See Copyright Notice in lua.h
*/

#define ldo_c
#define LUA_CORE

#include "lprefix.h"


#include <setjmp.h>
#include <stdlib.h>
#include <string.h>

#include "lua.h"

#include "lapi.h"
#include "ldebug.h"
#include "ldo.h"
#include "lfunc.h"
#include "lgc.h"
#include "lmem.h"
#include "lobject.h"
#include "lopcodes.h"
#include "lparser.h"
#include "lstate.h"
#include "lstring.h"
#include "ltable.h"
#include "ltm.h"
#include "lundump.h"
#include "lvm.h"
#include "lzio.h"



#define errorstatus(s)	((s) > LUA_YIELD)


/*
** {======================================================
** Error-recovery functions
** =======================================================
*/

/*
** LUAI_THROW/LUAI_TRY define how Lua does exception handling. By
** default, Lua handles errors with exceptions when compiling as
** C++ code, with _longjmp/_setjmp when asked to use them, and with
** longjmp/setjmp otherwise.
*/
// 如果没有定义异常宏，开始定义 
#if !defined(LUAI_THROW)				/* { */

// 情形1, 使用C++编译且没有强制指定必须用LUA_USE_LONGJMP, 把异常采用C++的try catch实现
#if defined(__cplusplus) && !defined(LUA_USE_LONGJMP)	/* { */

/* C++ exceptions */
#define LUAI_THROW(L,c)		throw(c)
#define LUAI_TRY(L,c,a) \
	try { a } catch(...) { if ((c)->status == 0) (c)->status = -1; }
#define luai_jmpbuf		int  /* dummy variable */ // 用c++异常就不要这个变量

#elif defined(LUA_USE_POSIX)				/* }{ */

/* in POSIX, try _longjmp/_setjmp (more efficient) */
/* 情形2, 使用POSIX的话, 异常通过 _longjmp/_setjmp 实现, 更为高效 */
#define LUAI_THROW(L,c)		_longjmp((c)->b, 1)
#define LUAI_TRY(L,c,a)		if (_setjmp((c)->b) == 0) { a }
#define luai_jmpbuf		jmp_buf

#else							/* }{ */

/* ISO C handling with long jumps */
/* 情形3, 采用标准C来处理 */
#define LUAI_THROW(L,c)		longjmp((c)->b, 1) // longjmp读档成功后,其实代码就返回到了下面setjmp所在的位置了。神奇的返回！！！
#define LUAI_TRY(L,c,a)		if (setjmp((c)->b) == 0) { a }
#define luai_jmpbuf		jmp_buf

#endif							/* } */

#endif							/* } */ // end #if !defined(LUAI_THROW)



/* chain list of long jump buffers */
struct lua_longjmp {
  struct lua_longjmp *previous;
  luai_jmpbuf b;
  volatile int status;  /* error code */
};


static void seterrorobj (lua_State *L, int errcode, StkId oldtop) {
  switch (errcode) {
    case LUA_ERRMEM: {  /* memory error? */
      setsvalue2s(L, oldtop, G(L)->memerrmsg); /* reuse preregistered msg. */
      break;
    }
    case LUA_ERRERR: {
      setsvalue2s(L, oldtop, luaS_newliteral(L, "error in error handling"));
      break;
    }
    default: {
      setobjs2s(L, oldtop, L->top - 1);  /* error message on current top */
      break;
    }
  }
  L->top = oldtop + 1;
}


l_noret luaD_throw (lua_State *L, int errcode) {
  if (L->errorJmp) {  /* thread has an error handler? */
    L->errorJmp->status = errcode;  /* set status */
    LUAI_THROW(L, L->errorJmp);  /* jump to it */
  }
  else {  /* thread has no error handler */
    // 发生了异常，但是错误处理链里米有可以处理的...
    global_State *g = G(L);
    // 标记本线程已死
    L->status = cast_byte(errcode);  /* mark it as dead */
    if (g->mainthread->errorJmp) {  /* main thread has a handler? */
      // 主线程能搞的话，把错误对象保存到主线程栈顶
      setobjs2s(L, g->mainthread->top++, L->top - 1);  /* copy error obj. */
      // 向主线程抛出异常
      luaD_throw(g->mainthread, errcode);  /* re-throw in main thread */
    }
    else {  /* no handler at all; abort */
      // 撒？主线程没有处理程序, 那...调panic函数吧
      if (g->panic) {  /* panic function? */
        seterrorobj(L, errcode, L->top);  /* assume EXTRA_STACK */
        if (L->ci->top < L->top)
          L->ci->top = L->top;  /* pushing msg. can break this invariant */
        lua_unlock(L);
        g->panic(L);  /* call panic function (last chance to jump out) */
      }
      // 暴力终止
      abort();
    }
  }
}


int luaD_rawrunprotected (lua_State *L, Pfunc f, void *ud) {
  unsigned short oldnCcalls = L->nCcalls;
  // 设置新的lua_longjmp串到链表上
  struct lua_longjmp lj;
  lj.status = LUA_OK;
  lj.previous = L->errorJmp;  /* chain new error handler */
  L->errorJmp = &lj;
  // 首先调用setjmp(lj.b),如果返回0,表示设置成功，然后就调用函数(*f)(L, ud)
  // 这里所谓的保护模式，就是在正式运行函数f之前，通过setjmp保存当前的堆栈寄存器等，如果f函数在运行过程中(等同f函数内嵌套其他无论多少层函数), 如果发生了错误
  // 会通过 throw 直接回到这里
  LUAI_TRY(L, &lj,
    (*f)(L, ud);
  );
  // 已经执行完了f函数，肯定不用继续保护了
  // 恢复之前的错误处理链,就是把前面新加入的 lua_longjmp 结构去掉，恢复之前的状态
  L->errorJmp = lj.previous;  /* restore old error handler */
  L->nCcalls = oldnCcalls;
  // 但是最后需要返回在函数调用过程的结果，一般是米有异常发生为0，有异常是1
  return lj.status;
}

/* }====================================================== */


/*
** {==================================================================
** Stack reallocation
** ===================================================================
*/
static void correctstack (lua_State *L, TValue *oldstack) {
  // 修正upvalue以及执行栈对数据栈的引用
  CallInfo *ci;
  UpVal *up;
  L->top = (L->top - oldstack)/*栈修正后的长度*/ + L->stack/*当前的栈低*/;
  for (up = L->openupval; up != NULL; up = up->u.open.next)
    up->v = (up->v - oldstack)/*upvalue的相对栈底偏移*/ + L->stack;
  for (ci = L->ci; ci != NULL; ci = ci->previous) {
    // 父级调用 CallInfo 链修正
    ci->top = (ci->top - oldstack) + L->stack;
    ci->func = (ci->func - oldstack) + L->stack;
    if (isLua(ci))
      ci->u.l.base = (ci->u.l.base - oldstack) + L->stack;
  }
}


/* some space for error handling */
#define ERRORSTACKSIZE	(LUAI_MAXSTACK + 200)


void luaD_reallocstack (lua_State *L, int newsize) {
  TValue *oldstack = L->stack;
  int lim = L->stacksize;
  lua_assert(newsize <= LUAI_MAXSTACK || newsize == ERRORSTACKSIZE);
  lua_assert(L->stack_last - L->stack == L->stacksize - EXTRA_STACK);
  // realloc本来自带把数组老的拷贝到新的的功能
  luaM_reallocvector(L, L->stack, L->stacksize, newsize, TValue);
  // 把多出来的数据设置nil
  for (; lim < newsize; lim++)
    setnilvalue(L->stack + lim); /* erase new segment */
  L->stacksize = newsize;
  L->stack_last = L->stack + newsize - EXTRA_STACK;
  // 修正upvalue和CallInfo链上的地址
  correctstack(L, oldstack);
}


void luaD_growstack (lua_State *L, int n) {
  // 检查size最后通过luaD_reallocstack来实际增长栈
  int size = L->stacksize;
  if (size > LUAI_MAXSTACK)  /* error after extra size? */
    luaD_throw(L, LUA_ERRERR);
  else {
    int needed = cast_int(L->top - L->stack) + n + EXTRA_STACK;
    int newsize = 2 * size;
    if (newsize > LUAI_MAXSTACK) newsize = LUAI_MAXSTACK;
    if (newsize < needed) newsize = needed;
    if (newsize > LUAI_MAXSTACK) {  /* stack overflow? */
      luaD_reallocstack(L, ERRORSTACKSIZE);
      luaG_runerror(L, "stack overflow");
    }
    else
      luaD_reallocstack(L, newsize);
  }
}


static int stackinuse (lua_State *L) {
  CallInfo *ci;
  StkId lim = L->top;
  // 遍历整个State的ci链，找到醉倒的ci的栈顶
  for (ci = L->ci; ci != NULL; ci = ci->previous) {
    lua_assert(ci->top <= L->stack_last);
    if (lim < ci->top) lim = ci->top;
  }
  return cast_int(lim - L->stack) + 1;  /* part of stack in use */
}


void luaD_shrinkstack (lua_State *L) {
  int inuse = stackinuse(L);
  int goodsize = inuse + (inuse / 8) + 2*EXTRA_STACK;
  if (goodsize > LUAI_MAXSTACK) goodsize = LUAI_MAXSTACK;
  if (L->stacksize > LUAI_MAXSTACK)  /* was handling stack overflow? */
    luaE_freeCI(L);  /* free all CIs (list grew because of an error) */
  else
    luaE_shrinkCI(L);  /* shrink list */
  if (inuse <= LUAI_MAXSTACK &&  /* not handling stack overflow? */
      goodsize < L->stacksize)  /* trying to shrink? */
    luaD_reallocstack(L, goodsize);  /* shrink it */
  else
    condmovestack(L,,);  /* don't change stack (change only for debugging) */
}


void luaD_inctop (lua_State *L) {
  // 检查top增加一个后会不会触顶到 last_stack, 否则就要适时调用luaD_growstack
  luaD_checkstack(L, 1);
  L->top++;
}

/* }================================================================== */


/*
** Call a hook for the given event. Make sure there is a hook to be
** called. (Both 'L->hook' and 'L->hookmask', which triggers this
** function, can be changed asynchronously by signals.)
*/
void luaD_hook (lua_State *L, int event, int line) {
  lua_Hook hook = L->hook;
  if (hook && L->allowhook) {  /* make sure there is a hook */
    CallInfo *ci = L->ci;
    // 保存栈
    ptrdiff_t top = savestack(L, L->top);
    ptrdiff_t ci_top = savestack(L, ci->top);
    // 构造调试信息
    lua_Debug ar;
    ar.event = event;
    ar.currentline = line;
    ar.i_ci = ci;
    luaD_checkstack(L, LUA_MINSTACK);  /* ensure minimum stack size */
    ci->top = L->top + LUA_MINSTACK;
    lua_assert(ci->top <= L->stack_last);
    // 禁用钩子，防止递归调用
    L->allowhook = 0;  /* cannot call hooks inside a hook */
    ci->callstatus |= CIST_HOOKED;
    lua_unlock(L);
    // 调用C的钩子函数
    (*hook)(L, &ar);
    lua_lock(L);
    lua_assert(!L->allowhook);
    // 恢复现场
    L->allowhook = 1;
    ci->top = restorestack(L, ci_top);
    L->top = restorestack(L, top);
    ci->callstatus &= ~CIST_HOOKED;
  }
}


static void callhook (lua_State *L, CallInfo *ci) {
  int hook = LUA_HOOKCALL;
  ci->u.l.savedpc++;  /* hooks assume 'pc' is already incremented */
  // 检查改调用钩子是否属于尾调用，尾调用会产生优化操作，所以需要特殊标记处理
  if (isLua(ci->previous) &&
      GET_OPCODE(*(ci->previous->u.l.savedpc - 1)) == OP_TAILCALL) {
    ci->callstatus |= CIST_TAIL;
    hook = LUA_HOOKTAILCALL;
  }
  luaD_hook(L, hook, -1);
  ci->u.l.savedpc--;  /* correct 'pc' */
}


// 变长参数的函数的参数位置的修正
static StkId adjust_varargs (lua_State *L, Proto *p, int actual) {
  int i;
  // actual是在运行过程中真正传入的参数数量
  // nfixargs是函数定义的时候固定的参数数量, 一般nfixargs <= actual
  int nfixargs = p->numparams;
  StkId base, fixed;
  /* move fixed parameters to final position */
  fixed = L->top - actual;  /* first fixed argument */ // 第一个固定参数所在位置
  base = L->top;  /* final position of first argument */
  for (i = 0; i < nfixargs && i < actual; i++) {
    setobjs2s(L, L->top++, fixed + i); // 把参数的位置挨个挨个向后移
    setnilvalue(fixed + i);  /* erase original copy (for GC) */ // 原来位置的设为nil，好让GC回收
  }
  for (; i < nfixargs; i++) // 如果传入的 actual < nfixargs,帮着补全剩下的参数为nil
    setnilvalue(L->top++);  /* complete missing arguments */
  return base;
}


/*
** Check whether __call metafield of 'func' is a function. If so, put
** it in stack below original 'func' so that 'luaD_precall' can call
** it. Raise an error if __call metafield is not a function.
*/
// lua定义, 通过元方法进行函数调用和通过原生函数调用有区别。通过元方法进行函数调用的时候，需要把自身作为第一个参数传入
// 所以下面就是移动数据栈，把原参数们向后移，空出一格把自己插入
static void tryfuncTM (lua_State *L, StkId func) {
  const TValue *tm = luaT_gettmbyobj(L, func, TM_CALL);
  StkId p;
  if (!ttisfunction(tm))
    luaG_typeerror(L, func, "call");
  /* Open a hole inside the stack at 'func' */
  for (p = L->top; p > func; p--)
    setobjs2s(L, p, p-1);
  L->top++;  /* slot ensured by caller */
  setobj2s(L, func, tm);  /* tag method is the new function to be called */
}



// 有就移过去，没有就新建一个，移过去
#define next_ci(L) (L->ci = (L->ci->next ? L->ci->next : luaE_extendCI(L)))


/* macro to check stack size, preserving 'p' */
#define checkstackp(L,n,p)  \
  luaD_checkstackaux(L, n, \
    ptrdiff_t t__ = savestack(L, p);  /* save 'p' */ \
    luaC_checkGC(L),  /* stack grow uses memory */ \
    p = restorestack(L, t__))  /* 'pos' part: restore 'p' */


/*
** Prepares a function call: checks the stack, creates a new CallInfo
** entry, fills in the relevant information, calls hook if needed.
** If function is a C function, does the call, too. (Otherwise, leave
** the execution ('luaV_execute') to the caller, to allow stackless
** calls.) Returns true iff function has been executed (C function).
*/
// 返回1表示C函数，返回0表示lua函数
int luaD_precall (lua_State *L, StkId func, int nresults) {
  lua_CFunction f;
  CallInfo *ci;
  switch (ttype(func)) {
    case LUA_TCCL:  /* C closure */
      f = clCvalue(func)->f;
      goto Cfunc;
    case LUA_TLCF:  /* light C function */
      f = fvalue(func);
     Cfunc: {
      int n;  /* number of returns */
      checkstackp(L, LUA_MINSTACK, func);  /* ensure minimum stack size */
      ci = next_ci(L);  /* now 'enter' new function */
      ci->nresults = nresults;
      ci->func = func;
      // 云风: LUA_MINSTACK 默认20，在lua.h中。任何一次lua的C函数调用，都只保证这么大的数据栈空闲可用
      //       LUA供C使用的栈相关API都是不检查栈越界的，这是因为通常我们编写C拓展都能把数据栈空间控制在LUA_MINSTACK以内，或是显示拓展
      ci->top = L->top + LUA_MINSTACK;
      lua_assert(ci->top <= L->stack_last);
      ci->callstatus = 0;
      // 如果有设置回调，要回调
      if (L->hookmask & LUA_MASKCALL)
        luaD_hook(L, LUA_HOOKCALL, -1);
      lua_unlock(L);
      // C函数直接调用
      n = (*f)(L);  /* do the actual call */
      lua_lock(L);
      api_checknelems(L, n);
      // 函数返回收尾工作,移动CI,移动返回值等
      luaD_poscall(L, ci, L->top - n, n);
      return 1;
    }
    case LUA_TLCL: {  /* Lua function: prepare its call */
      StkId base;
      Proto *p = clLvalue(func)->p;
      int n = cast_int(L->top - func) - 1;  /* number of real arguments */
      int fsize = p->maxstacksize;  /* frame size */
      checkstackp(L, fsize, func);
      if (p->is_vararg != 1) {  /* do not use vararg? */
        for (; n < p->numparams; n++) // 传入的参数数量小于定义的参数数量, 把少去的补足当nil处理
          setnilvalue(L->top++);  /* complete missing arguments */
        base = func + 1;
      }
      else
        base = adjust_varargs(L, p, n);
      // 构造CI
      ci = next_ci(L);  /* now 'enter' new function */
      ci->nresults = nresults;
      ci->func = func;
      ci->u.l.base = base;
      // base是第一个参数所在的位置,被定义为一个栈帧的开始
      // Q?Q 为何直接就加了这个maxstacksize, 难道这个maxstacksize就能准确的估算整个数据栈所需空间？难道这个大小就是256个寄存器？
      L->top = ci->top = base + fsize;
      lua_assert(ci->top <= L->stack_last);
      ci->u.l.savedpc = p->code;  /* starting point */
      ci->callstatus = CIST_LUA;
      // 钩子
      if (L->hookmask & LUA_MASKCALL)
        callhook(L, ci);
      return 0;
    }
    default: {  /* not a function */
      // 最后的是说有的对象是通过元表驱动函数调用行为的, 所以这个时候需要通过 tryfuncTM 函数取得真正的调用函数
      checkstackp(L, 1, func);  /* ensure space for metamethod */
      tryfuncTM(L, func);  /* try to get '__call' metamethod */
      return luaD_precall(L, func, nresults);  /* now it must be a function */
    }
  }
}



/*
** Given 'nres' results at 'firstResult', move 'wanted' of them to 'res'.
** Handle most typical cases (zero results for commands, one result for
** expressions, multiple results for tail calls/single parameters)
** separated.
*/
// firstResult 第一个返回值目前所在的位置
// res 第一个返回值需要最终所需要在的位置
// nres 实际返回值的个数
// wanted 返回值预期所该有的个数，多余的抛弃，不足的补nil
// 返回值： 除了LUA_MULTRET这种不设上限的会返回0，其他情况都会返回1
static int moveresults (lua_State *L, const TValue *firstResult, StkId res,
                                      int nres, int wanted) {
  switch (wanted) {  /* handle typical cases separately */
    case 0: break;  /* nothing to move */ // 情况1. 本来就不需要返回值的直接跳出
    case 1: {  /* one result needed */    // 情况2. 需要一个返回值的
      if (nres == 0)   /* no results? */ // 哈？需要一个返回值但是实际却没返回值？那补一个
        firstResult = luaO_nilobject;  /* adjust with nil */
      setobjs2s(L, res, firstResult);  /* move it to proper place */
      break;
    }
    case LUA_MULTRET: { // 情况3. -1, 表示不设上限，有多少返回值要多少返回值
      int i;
      for (i = 0; i < nres; i++)  /* move all results to correct place */ // 把所有的返回值挨个放到目标位置，也就是原来函数栈数据部开始的地方
        setobjs2s(L, res + i, firstResult + i);
      L->top = res + nres; // 移了辣么多，肯定要移动top顶指针咯
      return 0;  /* wanted == LUA_MULTRET */
    }
    default: { // 情况4，返回值个数大于1的有限数
      int i;
      if (wanted <= nres) {  /* enough results? */
        // 个数特别多，超过wanted，把多余的丢弃
        for (i = 0; i < wanted; i++)  /* move wanted results to correct place */
          setobjs2s(L, res + i, firstResult + i);
      }
      else {  /* not enough results; use all of them plus nils */
        // 个数不够wanted，先把有的移动到目标位置，然后剩下的补充为nil
        for (i = 0; i < nres; i++)  /* move all results to correct place */
          setobjs2s(L, res + i, firstResult + i);
        for (; i < wanted; i++)  /* complete wanted number of results */
          setnilvalue(res + i);
      }
      break;
    }
  }
  // 除了LUA_MULTRET会提前返回，其他情况都会到这里，根据wanted调整top栈顶指针
  L->top = res + wanted;  /* top points after the last result */
  return 1;
}


/*
** Finishes a function call: calls hook if necessary, removes CallInfo,
** moves current number of results to proper place; returns 0 iff call
** wanted multiple (variable number of) results.
*/
// postfix call
// firstResult 当前栈指针Top - nres 所在 
// nres 实际函数调用后，产生的返回值数量
int luaD_poscall (lua_State *L, CallInfo *ci, StkId firstResult, int nres) {
  StkId res;
  int wanted = ci->nresults;
  if (L->hookmask & (LUA_MASKRET | LUA_MASKLINE)) {
    if (L->hookmask & LUA_MASKRET) { // 只有返回hook才会生效 Q?Q
      ptrdiff_t fr = savestack(L, firstResult);  /* hook may change stack */ // 调用钩子函数可能会改变栈，所以这里保存栈信息
      luaD_hook(L, LUA_HOOKRET, -1);
      firstResult = restorestack(L, fr);
    }
    // 只有有hook才会重置oldpc Q?Q
    L->oldpc = ci->previous->u.l.savedpc;  /* 'oldpc' for caller function */
  }
  res = ci->func;  /* res == final position of 1st result */ // 第一个返回值的最终归属，把调用函数本身都开始覆盖
  // 回到上级CI, 这里可以看出当函数结束的时候, CI调用栈信息并没有被立即销毁, 还存在链当中, 可能为了复用吧
  L->ci = ci->previous;  /* back to caller */
  /* move results to proper place */
  return moveresults(L, firstResult, res, nres, wanted);
}


/*
** Check appropriate error for stack overflow ("regular" overflow or
** overflow while handling stack overflow). If 'nCalls' is larger than
** LUAI_MAXCCALLS (which means it is handling a "regular" overflow) but
** smaller than 9/8 of LUAI_MAXCCALLS, does not report an error (to
** allow overflow handling to work)
*/
static void stackerror (lua_State *L) {
  if (L->nCcalls == LUAI_MAXCCALLS)
    luaG_runerror(L, "C stack overflow");
  else if (L->nCcalls >= (LUAI_MAXCCALLS + (LUAI_MAXCCALLS>>3)))
    luaD_throw(L, LUA_ERRERR);  /* error while handing stack error */
}


/*
** Call a function (C or Lua). The function to be called is at *func.
** The arguments are on the stack, right after the function. // 数据栈里，参数就在函数后面
** When returns, all the results are on the stack, starting at the original // 返回的时候所有的返回值被放在之前数据中函数所在的位置，差不多就是可能覆盖函数和其参数本身
** function position.
*/
// 这个函数是用来实现外部API lua_callk 之类的
void luaD_call (lua_State *L, StkId func, int nResults) {
  if (++L->nCcalls >= LUAI_MAXCCALLS)
    stackerror(L);
  if (!luaD_precall(L, func, nResults))  /* is a Lua function? */
    // 到了这里，说明这里是一个lua函数，前面的precall过程构造了新的CallInfo，下面调用execute后，会开始执行这个函数的字节码
    luaV_execute(L);  /* call it */
  // 这个函数肯定是一个C函数调用的，所以这里给lua_State说减少 nCalls 计数
  L->nCcalls--;
}


/*
** Similar to 'luaD_call', but does not allow yields during the call
*/
// 跟 luaD_call 一样，实际上这个功能原来就由 luaD_call 的一个参数来控制
// C语言本身无法支持延续点支持，所以lua也无法让所有的函数都是yieldable
// 当一级函数处于 non-yieldable 时，更深层次都无法yieldable。
// nny 全称 number of non-yieldable calls
void luaD_callnoyield (lua_State *L, StkId func, int nResults) {
  L->nny++;
  luaD_call(L, func, nResults);
  L->nny--;
}


/*
** Completes the execution of an interrupted C function, calling its
** continuation function.
** 这里是一一个C函数被断恢复成功后所需要的收尾工作，除了要完成原来被打断前应该有的后续工作，还要调用延续函数，通知表示该执行被打断过
*/
static void finishCcall (lua_State *L, int status) {
  CallInfo *ci = L->ci;
  int n;
  /* must have a continuation and must be able to call it */
  lua_assert(ci->u.c.k != NULL && L->nny == 0);
  /* error status can only happen in a protected call */
  lua_assert((ci->callstatus & CIST_YPCALL) || status == LUA_YIELD);
  if (ci->callstatus & CIST_YPCALL) {  /* was inside a pcall? */
    // 对应 pcallk 里在做 luaD_call(L, c.func, nresults); 之后的操作，如果函数在这个call里yield了，那就要帮助pcallk完成后面的清理工作
    ci->callstatus &= ~CIST_YPCALL;  /* finish 'lua_pcall' */
    L->errfunc = ci->u.c.old_errfunc;
  }
  /* finish 'lua_callk'/'lua_pcall'; CIST_YPCALL and 'errfunc' already
     handled */
  adjustresults(L, ci->nresults);
  /* call continuation function */
  lua_unlock(L);
  n = (*ci->u.c.k)(L, status, ci->u.c.ctx);
  lua_lock(L);
  api_checknelems(L, n);
  /* finish 'luaD_precall' */
  luaD_poscall(L, ci, L->top - n, n);
}


/*
** Executes "full continuation" (everything in the stack) of a
** previously interrupted coroutine until the stack is empty (or another
** interruption long-jumps out of the loop). If the coroutine is
** recovering from an error, 'ud' points to the error status, which must
** be passed to the first continuation function (otherwise the default
** status is LUA_YIELD).
*/
static void unroll (lua_State *L, void *ud) {
  if (ud != NULL)  /* error status? */
    finishCcall(L, *(int *)ud);  /* finish 'lua_pcallk' callee */
  // 只要CI链没有被回滚到base_ci, 就不断循环, postcall 会把ci = ci->previous
  // 除非这里发生了错误或者被YIELD了, 这个就被longjmp到了lua_resume里
  while (L->ci != &L->base_ci/*当前ci只要不是第一级ci*/) {  /* something in the stack */
    if (!isLua(L->ci))  /* C function? */
      // 之前被打断的是C函数, 通知让完成pcallk为完成的事情，然后额外要调用延续函数，最后主动调用postcall来移动返回值
      finishCcall(L, LUA_YIELD);  /* complete its execution */
    else {  /* Lua function */
      // 之前被打断的是lua函数调用，也就是说在lua的某条指令间接调用了call或者起元方法之类的然后被yield了。
      // 既然到了这里说明之前的调用已经有了返回值，就要去完成lua的指令的收尾工作，比如把结果移到A寄存器之类的
      luaV_finishOp(L);  /* finish interrupted instruction */
      // 已经完成上条未完成的指令恢复后应该有的一些工作，继续进行指令loop
      luaV_execute(L);  /* execute down to higher C 'boundary' */
    }
  }
}


/*
** Try to find a suspended protected call (a "recover point") for the
** given thread.
*/
static CallInfo *findpcall (lua_State *L) {
  CallInfo *ci;
  for (ci = L->ci; ci != NULL; ci = ci->previous) {  /* search for a pcall */
    if (ci->callstatus & CIST_YPCALL)
      return ci;
  }
  return NULL;  /* no pending pcall */
}


/*
** 从一个发生错误的协程里尝试恢复，一般是找到恢复点，就是发生 luaD_pcall 的那个栈, 把错误信息放到栈顶，把lua_State的ci回退到那个时候, 一般外面再用unroll去处理
** Recovers from an error in a coroutine. Finds a recover point (if
** there is one) and completes the execution of the interrupted
** 'luaD_pcall'. If there is no recover point, returns zero.
*/
static int recover (lua_State *L, int status) {
  StkId oldtop;
  CallInfo *ci = findpcall(L);
  if (ci == NULL) return 0;  /* no recovery point */
  /* "finish" luaD_pcall */
  // 这次 lua_pcallk 一定是在luaD_pcall中被打断
  oldtop = restorestack(L, ci->extra);
  // 要回退栈到当初 setjmp 那里,所以这之间被open的upvalue，需要关掉
  luaF_close(L, oldtop);
  // 把status 相关的错误信息，放到oldtop上去
  seterrorobj(L, status, oldtop);
  L->ci = ci;
  L->allowhook = getoah(ci->callstatus);  /* restore original 'allowhook' */
  L->nny = 0;  /* should be zero to be yieldable */ // nny一般不能大于1，这里其实相当于--nny，在nny值为1的情况下
  luaD_shrinkstack(L);
  L->errfunc = ci->u.c.old_errfunc;
  return 1;  /* continue running the coroutine */
}


/*
** signal an error in the call to 'resume', not in the execution of the
** coroutine itself. (Such errors should not be handled by any coroutine
** error handler and should not kill the coroutine.)
*/
static l_noret resume_error (lua_State *L, const char *msg, StkId firstArg) {
  L->top = firstArg;  /* remove args from the stack */
  setsvalue2s(L, L->top, luaS_new(L, msg));  /* push error message */
  api_incr_top(L);
  luaD_throw(L, -1);  /* jump back to 'lua_resume' */
}


/*
** Do the work for 'lua_resume' in protected mode. Most of the work
** depends on the status of the coroutine: initial state, suspended
** inside a hook, or regularly suspended (optionally with a continuation
** function), plus erroneous cases: non-suspended coroutine or dead
** coroutine.
*/
static void resume (lua_State *L, void *ud) {
  int nCcalls = L->nCcalls;
  int n = *(cast(int*, ud));  /* number of arguments */
  StkId firstArg = L->top - n;  /* first argument */
  CallInfo *ci = L->ci;
  if (nCcalls >= LUAI_MAXCCALLS)
    resume_error(L, "C stack overflow", firstArg);
  if (L->status == LUA_OK) {  /* may be starting a coroutine */
    if (ci != &L->base_ci)  /* not in base level? */
      resume_error(L, "cannot resume non-suspended coroutine", firstArg);
    /* coroutine is in base level; start running it */
    if (!luaD_precall(L, firstArg - 1/*主函数所在的位置*/, LUA_MULTRET/*主函数不限返回值*/))  /* Lua function? */
      luaV_execute(L);  /* call it */
  }
  else if (L->status != LUA_YIELD) // 感觉把其他情况先排除在这里有什么讲究的样子
    resume_error(L, "cannot resume dead coroutine", firstArg);
  else {  /* resuming from previous yield */
    L->status = LUA_OK;  /* mark that it is running (again) */
    ci->func = restorestack(L, ci->extra); // yield之前把主函数存 extra 的
    if (isLua(ci))  /* yielded inside a hook? */ 
      // 上次是在lua函数中的hook函数里yield的，继续lua的code
      luaV_execute(L);  /* just continue running Lua code */
    else {  /* 'common' yield */
      // 从C函数里yield的要检查它有没有设置延续函数，有的话要继续ta的延续函数
      if (ci->u.c.k != NULL) {  /* does it have a continuation function? */
        lua_unlock(L);
        // 调用延续函数，并把其返回值之类的设置起来，替代当初被yield的函数应该有的结果
        n = (*ci->u.c.k)(L, LUA_YIELD, ci->u.c.ctx); /* call continuation */
        lua_lock(L);
        api_checknelems(L, n);
        firstArg = L->top - n;  /* yield results come from continuation */
      }
      luaD_poscall(L, ci, firstArg, n);  /* finish 'luaD_precall' */
    }
    unroll(L, NULL);  /* run continuation */
  }
  lua_assert(nCcalls == L->nCcalls);
}


// from表示要启动或者恢复的协程是从哪个协程来的, 不存在可以是NULL
LUA_API int lua_resume (lua_State *L, lua_State *from, int nargs) {
  int status;
  unsigned short oldnny = L->nny;  /* save "number of non-yieldable" calls */
  lua_lock(L);
  luai_userstateresume(L, nargs);
  // 已经有多少嵌套的C调用了
  L->nCcalls = (from) ? from->nCcalls + 1 : 1;
  // 这是新启的协程或者继续运行的协程，所以nny = 0允许被yield
  L->nny = 0;  /* allow yields */
  // 如果状态是LUA_OK，表示要启动的这个协程是个萌新，栈上是主函数和ta的nargs个参数，所以这里要+1
  api_checknelems(L, (L->status == LUA_OK) ? nargs + 1 : nargs);
  // 对resume函数进行保护调用
  status = luaD_rawrunprotected(L, resume, &nargs);
  // 这里如果返回，表明一个协程的返回
  if (status == -1)  /* error calling 'lua_resume'? */
    status = LUA_ERRRUN;
  else {  /* continue running after recoverable errors */
    // errorstatus(status) 要是true，只有状态不是 YIELD 和 OK, 如果执行正常的话，下面的while和if都不会进入
    while (errorstatus(status) && recover(L, status)) { // 如果存在错误，尝试把ci恢复到当初setjmp的那个ci去
      /* unroll continuation */
      // 已经成功回退到 pcall 出错的那个CI了，接下来调用unroll是处理当时未完成的事业，相当于让这个CI延续运行下去，直到正常返回或者又特么被 YIELD 了
      // 那while里的过程又会尝试去恢复, 如果状态不是错误，或者恢复不了，就跳出去准备结束了
      status = luaD_rawrunprotected(L, unroll, &status);
    }
    if (errorstatus(status)) {  /* unrecoverable error? */
      // 错误持续存在, 这个错误没有被上面的while循环洗干净, 把错误对象放在栈顶
      // 在发生错误的情况下， 堆栈没有展开， 因此你可以使用调试 API 来处理它。 错误消息放在栈顶在。
      L->status = cast_byte(status);  /* mark thread as 'dead' */
      seterrorobj(L, status, L->top);  /* push error message */
      L->ci->top = L->top;
    }
    else lua_assert(status == L->status);  /* normal end or yield */
  }
  L->nny = oldnny;  /* restore 'nny' */
  L->nCcalls--;
  lua_assert(L->nCcalls == ((from) ? from->nCcalls : 0));
  lua_unlock(L);
  // 退出协程，正常返回 LUA_OK , 否则返回错误码, 错误信息被放在栈顶
  // 返回YIELD的话，可能还会被复活
  return status;
}


LUA_API int lua_isyieldable (lua_State *L) {
  return (L->nny == 0);
}


// lua_yieldk 是一个C API，只用于给lua程序编写C拓展模块使用
// 处于这个函数当中一定是处于一个C调用中, 这个函数必然是从 luaD_call 或 luaD_pcall 中退出。就是这两函数的的TRY的那个地方。那个地方打了断点后调用了f函数，这个yield一定处于f函数的内层
// 但是钩子函数的运行是个例外，钩子函数本身是一个C函数，但是不是通常的C API调用进来的
LUA_API int lua_yieldk (lua_State *L, int nresults, lua_KContext ctx,
                        lua_KFunction k) {
  CallInfo *ci = L->ci;
  luai_userstateyield(L, nresults);
  lua_lock(L);
  api_checknelems(L, nresults);
  if (L->nny > 0) {
    if (L != G(L)->mainthread)
      luaG_runerror(L, "attempt to yield across a C-call boundary");
    else
      luaG_runerror(L, "attempt to yield from outside a coroutine");
  }
  // 标记线程状态为LUA_YIELD
  L->status = LUA_YIELD;
  // 把当前执行函数保存到CallInfo的extra中
  ci->extra = savestack(L, ci->func);  /* save current 'func' */
  if (isLua(ci)) {  /* inside a hook? */
    // 我猜这里是指在钩子函数(C函数)里有什么行为调用yield，云风大侠说这里无法正确处理延续点，所以禁止传入延续点,暂时不是太理解
    // 钩子函数的yield线程就设置前面的状态，但是没有throw什么的 Q?Q
    api_check(L, k == NULL, "hooks cannot continue after yielding");
  }
  else {
    if ((ci->u.c.k = k) != NULL)  /* is there a continuation? */
      ci->u.c.ctx = ctx;  /* save context */
    ci->func = L->top - nresults - 1;  /* protect stack below results */
    // 这里讲道理的话，是不会返回了，回会退到C层面上上级某个调用 setjmp 的地方, 应该是 luaD_call 或 luaD_pcall 中 TRY 的那个地方
    luaD_throw(L, LUA_YIELD);
  }
  lua_assert(ci->callstatus & CIST_HOOKED);  /* must be inside a hook */
  lua_unlock(L);
  return 0;  /* return to 'luaD_hook' */
}


// 采用保护模式调用C函数
int luaD_pcall (lua_State *L, Pfunc func, void *u,
                ptrdiff_t old_top, ptrdiff_t ef) {
  int status;
  // 保存关键数据在这里的C栈上
  CallInfo *old_ci = L->ci;
  lu_byte old_allowhooks = L->allowhook;
  unsigned short old_nny = L->nny;
  ptrdiff_t old_errfunc = L->errfunc;
  L->errfunc = ef;
  // 采用会存档的方式运行 func 函数 
  status = luaD_rawrunprotected(L, func, u);
  if (status != LUA_OK) {  /* an error occurred? */
    // 调用失败，恢复保存的关键数据
    StkId oldtop = restorestack(L, old_top);
    luaF_close(L, oldtop);  /* close possible pending closures */
    seterrorobj(L, status, oldtop);
    L->ci = old_ci;
    L->allowhook = old_allowhooks;
    L->nny = old_nny;
    // 收缩CI链长度
    luaD_shrinkstack(L);
  }
  L->errfunc = old_errfunc;
  return status;
}



/*
** Execute a protected parser.
*/
struct SParser {  /* data to 'f_parser' */
  ZIO *z;
  Mbuffer buff;  /* dynamic structure used by the scanner */
  Dyndata dyd;  /* dynamic structures used by the parser */
  const char *mode;
  const char *name;
};


static void checkmode (lua_State *L, const char *mode, const char *x) {
  if (mode && strchr(mode, x[0]) == NULL) {
    luaO_pushfstring(L,
       "attempt to load a %s chunk (mode is '%s')", x, mode);
    luaD_throw(L, LUA_ERRSYNTAX);
  }
}


static void f_parser (lua_State *L, void *ud) {
  LClosure *cl;
  struct SParser *p = cast(struct SParser *, ud);
  int c = zgetc(p->z);  /* read first character */
  if (c == LUA_SIGNATURE[0]) {
    checkmode(L, p->mode, "binary");
    cl = luaU_undump(L, p->z, p->name);
  }
  else {
    checkmode(L, p->mode, "text");
    cl = luaY_parser(L, p->z, &p->buff, &p->dyd, p->name, c);
  }
  lua_assert(cl->nupvalues == cl->p->sizeupvalues);
  luaF_initupvals(L, cl);
}


int luaD_protectedparser (lua_State *L, ZIO *z, const char *name,
                                        const char *mode) {
  struct SParser p;
  int status;
  L->nny++;  /* cannot yield during parsing */
  p.z = z; p.name = name; p.mode = mode;
  p.dyd.actvar.arr = NULL; p.dyd.actvar.size = 0;
  p.dyd.gt.arr = NULL; p.dyd.gt.size = 0;
  p.dyd.label.arr = NULL; p.dyd.label.size = 0;
  luaZ_initbuffer(L, &p.buff);
  status = luaD_pcall(L, f_parser, &p, savestack(L, L->top), L->errfunc);
  luaZ_freebuffer(L, &p.buff);
  luaM_freearray(L, p.dyd.actvar.arr, p.dyd.actvar.size);
  luaM_freearray(L, p.dyd.gt.arr, p.dyd.gt.size);
  luaM_freearray(L, p.dyd.label.arr, p.dyd.label.size);
  L->nny--;
  return status;
}


