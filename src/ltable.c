/*
** $Id: ltable.c,v 2.117 2015/11/19 19:16:22 roberto Exp $
** Lua tables (hash)
** See Copyright Notice in lua.h
*/

#define ltable_c
#define LUA_CORE

#include "lprefix.h"


/*
** Implementation of tables (aka arrays, objects, or hash tables).
** Tables keep its elements in two parts: an array part and a hash part.
** Non-negative integer keys are all candidates to be kept in the array
** part. The actual size of the array is the largest 'n' such that
** more than half the slots between 1 and n are in use.
** Hash uses a mix of chained scatter table with Brent's variation.
** A main invariant of these tables is that, if an element is not
** in its main position (i.e. the 'original' position that its hash gives
** to it), then the colliding element is in its own main position.
** Hence even when the load factor reaches 100%, performance remains good.
*/

#include <math.h>
#include <limits.h>

#include "lua.h"

#include "ldebug.h"
#include "ldo.h"
#include "lgc.h"
#include "lmem.h"
#include "lobject.h"
#include "lstate.h"
#include "lstring.h"
#include "ltable.h"
#include "lvm.h"


/*
** Maximum size of array part (MAXASIZE) is 2^MAXABITS. MAXABITS is
** the largest integer such that MAXASIZE fits in an unsigned int.
*/
// 所以这个MAXABITS是31
#define MAXABITS	cast_int(sizeof(int) * CHAR_BIT - 1)
#define MAXASIZE	(1u << MAXABITS)

/*
** Maximum size of hash part is 2^MAXHBITS. MAXHBITS is the largest
** integer such that 2^MAXHBITS fits in a signed int. (Note that the
** maximum number of elements in a table, 2^MAXABITS + 2^MAXHBITS, still
** fits comfortably in an unsigned int.)
*/
// hash部分30位
#define MAXHBITS	(MAXABITS - 1)


#define hashpow2(t,n)		(gnode(t, lmod((n), sizenode(t))))

#define hashstr(t,str)		hashpow2(t, (str)->hash)    // 用字符串的hash值去对table里的hash表的size做取摸运算
#define hashboolean(t,p)	hashpow2(t, p)              // 用0或者1去对 t.hashsize 取模咯
#define hashint(t,i)		hashpow2(t, i)                // int 值对 t.hashsize 取模


/*
** for some types, it is better to avoid modulus by power of 2, as
** they tend to have many 2 factors.
*/
#define hashmod(t,n)	(gnode(t, ((n) % ((sizenode(t)-1)|1))))


#define hashpointer(t,p)	hashmod(t, point2uint(p))


#define dummynode		(&dummynode_)

#define isdummy(n)		((n) == dummynode)

// 这是一个static const的节点，只能被读,指针指向这里了也不能随便乱改
static const Node dummynode_ = {
  {NILCONSTANT},  /* value */
  {{NILCONSTANT, 0}}  /* key */
};


/*
** Hash for floating-point numbers.
** The main computation should be just
**     n = frexp(n, &i); return (n * INT_MAX) + i
** but there are some numerical subtleties.
** In a two-complement representation, INT_MAX does not has an exact
** representation as a float, but INT_MIN does; because the absolute
** value of 'frexp' is smaller than 1 (unless 'n' is inf/NaN), the
** absolute value of the product 'frexp * -INT_MIN' is smaller or equal
** to INT_MAX. Next, the use of 'unsigned int' avoids overflows when
** adding 'i'; the use of '~u' (instead of '-u') avoids problems with
** INT_MIN.
** 本函数用于对浮点数求hash
** 主要计算过程可以描述为(有细微的处理):
**         n = frexp(n, &i); return (n * INT_MAX) + i; 
** frexp的返回值的绝对值区间是[0.5,1), 所以frexp * -INT_MIN <= INT_MAX, 紧接着的使用 uint 来相加避免了溢出
** 通过使用 ~u 而不是直接 -u 取负，避免了 INT_MIN 的问题:
**     当某个uint是1...(31个0),那这个数是2147483648，已经超过了INT_MAX(2147483647), 如果采用 -u, 会取反加1，那么二进制就变成了 0...(31个1) ---> 1...(31个0)，再变成int之后就成了 INT_MIN
**     如果采用取反的话，返回的int必定是一个小于等于 INT_MAX 的正整数
*/
#if !defined(l_hashfloat)
static int l_hashfloat (lua_Number n) {
  int i;
  lua_Integer ni;
  // frexp 把一个浮点数分解为尾数和指数, 传入的第一参数是被分解的数n，第二个参数是指数i，返回值是浮点尾数ret。 n = ret*2^i
  n = l_mathop(frexp)(n, &i) * -cast_num(INT_MIN);
  if (!lua_numbertointeger(n, &ni)) {  /* is 'n' inf/-inf/NaN? */
    lua_assert(luai_numisnan(n) || l_mathop(fabs)(n) == cast_num(HUGE_VAL));
    return 0;
  }
  else {  /* normal case */ // 上面的lua_numbertointeger返回1，表示n已经被round取整到了int
    unsigned int u = cast(unsigned int, i) + cast(unsigned int, ni); // 把之前分解出的指数和后面被转后的整数求和
    return cast_int(u <= cast(unsigned int, INT_MAX) ? u : ~u);
  }
}
#endif


/*
** returns the 'main' position of an element in a table (that is, the index
** of its hash value)
*/
static Node *mainposition (const Table *t, const TValue *key) {
  switch (ttype(key)) {
    case LUA_TNUMINT:
      return hashint(t, ivalue(key));
    case LUA_TNUMFLT:
      return hashmod(t, l_hashfloat(fltvalue(key)));
    case LUA_TSHRSTR:
      return hashstr(t, tsvalue(key));
    case LUA_TLNGSTR:
      return hashpow2(t, luaS_hashlongstr(tsvalue(key)));  // 长字符串采用luaS_hashlongstr做惰性计算
    case LUA_TBOOLEAN:
      return hashboolean(t, bvalue(key));
    case LUA_TLIGHTUSERDATA:
      return hashpointer(t, pvalue(key)); // 把指针转成一个unit，然后对table的size做mod运算
    case LUA_TLCF:
      return hashpointer(t, fvalue(key)); // 同上，不过是把函数指针转 unit
    default:
      lua_assert(!ttisdeadkey(key));
      return hashpointer(t, gcvalue(key));
  }
}


/*
** returns the index for 'key' if 'key' is an appropriate key to live in
** the array part of the table, 0 otherwise.
** 返回一个key在数组部分的index，如果这个key是正确存在于数组部分的key的话，否则就返回0
*/
static unsigned int arrayindex (const TValue *key) {
  if (ttisinteger(key)) {
    lua_Integer k = ivalue(key);
    if (0 < k && (lua_Unsigned)k <= MAXASIZE)
      return cast(unsigned int, k);  /* 'key' is an appropriate array index */
  }
  return 0;  /* 'key' did not match some condition */
}


/*
** returns the index of a 'key' for table traversals. First goes all
** elements in the array part, then elements in the hash part. The
** beginning of a traversal is signaled by 0.
*/
static unsigned int findindex (lua_State *L, Table *t, StkId key) {
  unsigned int i;
  if (ttisnil(key)) return 0;  /* first iteration */
  i = arrayindex(key);
  if (i != 0 && i <= t->sizearray)  /* is 'key' inside array part? */ 
    // 这个key存的index在数组部，返回数组索引
    return i;  /* yes; that's the index */
  else {
    int nx;
    Node *n = mainposition(t, key); // 先得到"讲道理"情况下mainpoint应该的槽位
    for (;;) {  /* check whether 'key' is somewhere in the chain */
      /* key may be dead already, but it is ok to use it in 'next' */
      if (luaV_rawequalobj(gkey(n), key) || // 该槽位存的东西跟key一猫一样
            (ttisdeadkey(gkey(n)) && iscollectable(key) && deadvalue(gkey(n)) == gcvalue(key)) // 该槽位key是死的，是可回收的，并且该key的gc指针指的是一个东西
            ) {
        i = cast_int(n - gnode(t, 0));  /* key index in hash table */ // 当前node点指针减去table的hash表头偏移等于key在hash部的index
        /* hash elements are numbered after array ones */
        return (i + 1) + t->sizearray; // hash索引值是紧接着array数组部后面编号的，加1是为了符合lua里从1开始数index？
      }
      nx = gnext(n); // 到下一个node的偏移量，因为到这里没有返回的话说明n可能和主键同hash但是不是同一个元素
      if (nx == 0)
        luaG_runerror(L, "invalid key to 'next'");  /* key not found */
      else n += nx; // 同一个hash的可能有多个值，依次顺着这条链找下去，直到找到
    }
  }
}


int luaH_next (lua_State *L, Table *t, StkId key) {
  unsigned int i = findindex(L, t, key);  /* find original element */ // 找到key本身所在，返回0就从0开始找咯，大于t->sizearray则表示索引在hash部分
  for (; i < t->sizearray; i++) {  /* try first array part */
    // 能进这里，表i返回的是在array数组部分，或者直接返回0，表示从头找
    if (!ttisnil(&t->array[i])) {  /* a non-nil value? */
      // i是array部分用于内部索引，返回给lua用户层要用从1开始数数组的方式
      setivalue(key, i + 1);
      // 把原始key对应的值拷贝到栈顶
      setobj2s(L, key+1, &t->array[i]);
      return 1;
    }
  }
  for (i -= t->sizearray; cast_int(i) < sizenode(t); i++) {  /* hash part */
    if (!ttisnil(gval(gnode(t, i)))) {  /* a non-nil value? */
      // 老规矩，替换key，把其value放在栈上
      setobj2s(L, key, gkey(gnode(t, i)));
      setobj2s(L, key+1, gval(gnode(t, i)));
      return 1;
    }
  }
  return 0;  /* no more elements */
}


/*
** {=============================================================
** Rehash
** ==============================================================
*/

/*
** 计算table数组部分最优的大小，nums存的是 在(2^(lg-1), l^lg], 其中0<lg<=31, 各个区段内存的键值对数量
** pna 则是table的array部分和hash部分里用正整数做key的总数
** 返回值:
**     返回的optimal是数组部分最优要开辟的部分
**     pna出去的时候则返回会被存到table数组部分的键值数量，这个值可能小于进来的时候的值，中间的差额的键值会被存到hash部分 
** Compute the optimal size for the array part of table 't'. 'nums' is a
** "count array" where 'nums[i]' is the number of integers in the table
** between 2^(i - 1) + 1 and 2^i. 'pna' enters with the total number of
** integer keys in the table and leaves with the number of keys that
** will go to the array part; return the optimal size.
*/
static unsigned int computesizes (unsigned int nums[], unsigned int *pna) {
  int i;
  unsigned int twotoi;  /* 2^i (candidate for optimal size) */
  unsigned int a = 0;  /* number of elements smaller than 2^i */
  unsigned int na = 0;  /* number of elements to go to array part */
  unsigned int optimal = 0;  /* optimal size for array part */
  /* loop while keys can fill more than half of total size */
  // twotoi = 2^i
  for (i = 0, twotoi = 1; *pna > twotoi / 2; i++, twotoi *= 2) {
    if (nums[i] > 0) {
      a += nums[i]; // 在 (0, 2^i] 区间内一共堆积了多少元素
      // 如果这些堆积的元素数量大于 2^i，必定小于2^(i+1)，也就是twotoi, 那么在当前区段的空间利用率必定大于50%
      if (a > twotoi/2) {  /* more than half elements present? */
        // 那么最优size就是 2^(i+1)，也就是twotoi
        optimal = twotoi;  /* optimal size (till now) */
        // 会被存到table的数组部分的元素数量
        na = a;  /* all elements up to 'optimal' will go to array part */
      }
    }
  }
  lua_assert((optimal == 0 || optimal / 2 < na) && na <= optimal);
  *pna = na;
  return optimal;
}


static int countint (const TValue *key, unsigned int *nums) {
  unsigned int k = arrayindex(key);
  if (k != 0) {  /* is 'key' an appropriate array index? */
    nums[luaO_ceillog2(k)]++;  /* count as such */
    return 1;
  }
  else
    return 0;
}


/*
** Count keys in array part of table 't': Fill 'nums[i]' with
** number of keys that will go into corresponding slice and return
** total number of non-nil keys.
** 返回两个:
**     1. nums装的是每个区间存的键值数， 比如nums[8], 存的就是键值hash区间为(2^7, 2^8]里存的键值的个数
**     2. ause是nums里每个位置的数的求和
*/
static unsigned int numusearray (const Table *t, unsigned int *nums) {
  int lg;
  unsigned int ttlg;  /* 2^lg */
  unsigned int ause = 0;  /* summation of 'nums' */
  unsigned int i = 1;  /* count to traverse all array keys */
  /* traverse each slice */
  for (lg = 0, ttlg = 1; lg <= MAXABITS/* = 31 */; lg++, ttlg *= 2) {
    unsigned int lc = 0;  /* counter */ // 用于计算当前(2^(lg - 1), 2^lg]区段存了多少个键值
    unsigned int lim = ttlg; // ttlg = 2^lg
    if (lim > t->sizearray) {
      // 如果当前区段超过了table的size，修正lim
      lim = t->sizearray;  /* adjust upper limit */
      // i是用来遍历整个table的array索引的，如果这里已经大于当前区段的最大值lim了，说明本区段及其后面的区段没什么好遍历的了，因为没有后面了，直接返回
      if (i > lim)
        break;  /* no more elements to count */
    }
    /* count elements in range (2^(lg - 1), 2^lg] */
    // 数出区段 (2^(lg - 1), 2^lg] 存了多少个键值
    for (; i <= lim; i++) {
      if (!ttisnil(&t->array[i-1]))
        lc++;
    }
    nums[lg] += lc;
    ause += lc;
  }
  return ause;
}


static int numusehash (const Table *t, unsigned int *nums, unsigned int *pna) {
  int totaluse = 0;  /* total number of elements */
  int ause = 0;  /* elements added to 'nums' (can go to array part) */
  // 从尾向首，依次遍历，访问hash部分的所有的node
  int i = sizenode(t);
  while (i--) {
    Node *n = &t->node[i];
    if (!ttisnil(gval(n))) { // 如果某node存在值
      // countint 对key做一些检查，ta的value部分被希望存在区间于 (0, MAXASIZE] 的一个uint，如果没什么问题的话，nums的对应区间位增加1，并返回1
      // 如果node的key的键值不是一个存在于(0, MAXASIZE]的正整数，那就返回0
      ause += countint(gkey(n), nums);
      // 即使上面返回0，nums什么也不加，这里依然会+1
      totaluse++;
    }
  }
  *pna += ause;
  // 返回table的hash部分存的有效键值的node的数量
  return totaluse;
}


static void setarrayvector (lua_State *L, Table *t, unsigned int size) {
  unsigned int i;
  luaM_reallocvector(L, t->array, t->sizearray, size, TValue);
  for (i=t->sizearray; i<size; i++)
     setnilvalue(&t->array[i]);
  t->sizearray = size;
}


static void setnodevector (lua_State *L, Table *t, unsigned int size) {
  int lsize;
  if (size == 0) {  /* no elements to hash part? */
    // 为了减少数据空间的维护成本，空表初始化设置指向这个不可修改的dummynode的只读节点
    t->node = cast(Node *, dummynode);  /* use common 'dummynode' */
    lsize = 0;
  }
  else {
    int i;
    lsize = luaO_ceillog2(size);
    if (lsize > MAXHBITS) // lsize不可以超过30
      luaG_runerror(L, "table overflow");
    size = twoto(lsize); // 二进制移位，求得马上要创建的array数组的size
    t->node = luaM_newvector(L, size, Node);
    // 初始化整个hash node节点
    for (i = 0; i < (int)size; i++) {
      Node *n = gnode(t, i);
      gnext(n) = 0;
      setnilvalue(wgkey(n));
      setnilvalue(gval(n));
    }
  }
  t->lsizenode = cast_byte(lsize); // 为了接受luaO_ceillog2才定义成int的，这里强制转回去
  t->lastfree = gnode(t, size);  /* all positions are free */
}


void luaH_resize (lua_State *L, Table *t, unsigned int nasize,
                                          unsigned int nhsize) {
  unsigned int i;
  int j;
  unsigned int oldasize = t->sizearray;
  int oldhsize = t->lsizenode;
  Node *nold = t->node;  /* save old hash ... */
  // 扩大table的数组部分，realloc会帮着拷贝数组，多出来的会被填nil
  if (nasize > oldasize)  /* array part must grow? */ // 数组部分要遭到扩张
    setarrayvector(L, t, nasize);
  /* create new hash part with appropriate size */
  // 开辟hash部分，只开辟赋nil，没有正式移动数据
  setnodevector(L, t, nhsize);
  if (nasize < oldasize) {  /* array part must shrink? */ // 数组部分要遭到收缩
    t->sizearray = nasize;
    /* re-insert elements from vanishing slice */
    // 先把多余的插入到hash部分
    for (i=nasize; i<oldasize; i++) {
      if (!ttisnil(&t->array[i]))
        luaH_setint(L, t, i + 1, &t->array[i]);
    }
    /* shrink array */
    // 用内存API收缩数组部分长度
    luaM_reallocvector(L, t->array, oldasize, nasize, TValue);
  }
  /* re-insert elements from hash part */
  // 把old的hash部分挨着挨着挨着新的hash部分里
  for (j = twoto(oldhsize) - 1; j >= 0; j--) {
    Node *old = nold + j;
    if (!ttisnil(gval(old))) {
      /* doesn't need barrier/invalidate cache, as entry was
         already present in the table */
      setobjt2t(L, luaH_set(L, t, gkey(old)), gval(old));
    }
  }
  if (!isdummy(nold))
    // 如果之前old不是一个空hash，那么释放这些数组部分
    luaM_freearray(L, nold, cast(size_t, twoto(oldhsize))); /* free old hash */
}


void luaH_resizearray (lua_State *L, Table *t, unsigned int nasize) {
  int nsize = isdummy(t->node) ? 0 : sizenode(t);
  luaH_resize(L, t, nasize, nsize);
}

/*
** nums[i] = number of keys 'k' where 2^(i - 1) < k <= 2^i
*/
static void rehash (lua_State *L, Table *t, const TValue *ek) {
  unsigned int asize;  /* optimal size for array part */
  unsigned int na;  /* number of keys in the array part */
  unsigned int nums[MAXABITS + 1];
  int i;
  int totaluse;
  for (i = 0; i <= MAXABITS; i++) nums[i] = 0;  /* reset counts */
  // na 统计的是array部分和hash部分所有的键值value是uint的node数量
  // nums 统计的在(2^(lg-1), l^lg], 其中0<lg<=31, 各个区段内键值value是uint的数量
  // totaluse 则表示所有array和hash部分的有效node的数量，key的value部可以不是正整数
  na = numusearray(t, nums);  /* count keys in array part */
  totaluse = na;  /* all those keys are integer keys */
  totaluse += numusehash(t, nums, &na);  /* count keys in hash part */
  /* count extra key */
  na += countint(ek, nums);
  totaluse++;
  /* compute new size for array part */
  asize = computesizes(nums, &na);
  /* resize the table to new computed sizes */
  luaH_resize(L, t, asize/*数组部分最优长*/, totaluse - na/*总的使用量减去会被放到数组部的长也就是hash部分最低需要的长*/);
}



/*
** }=============================================================
*/


// 一个table最多由三块连续内存构成
//     1. 存放了连续整数索引的数组
//     2. 一块大小为2的整数次幂的哈希表
//     3. Table 结构

Table *luaH_new (lua_State *L) {
  GCObject *o = luaC_newobj(L, LUA_TTABLE, sizeof(Table));
  Table *t = gco2t(o);
  t->metatable = NULL;
  t->flags = cast_byte(~0); // 用8个bit来标记前8个TM方法是否存在，这里初始化前8个完全不存在。8个之后的每次都要查
  t->array = NULL; // 数据部分默认为0，为空
  t->sizearray = 0;
  setnodevector(L, t, 0); // hash部分默认为0
  return t;
}


void luaH_free (lua_State *L, Table *t) {
  // 无论hash部还是数组部，都是连续的数组，所以通过realloc( ptr, 0 ), 收缩掉数据们
  if (!isdummy(t->node)) // hash部分不是初始的dummy节点，说明不是空hash部
    luaM_freearray(L, t->node, cast(size_t, sizenode(t)));
  luaM_freearray(L, t->array, t->sizearray);
  // 直接内存层面上释放整个 Table 结构, 整个本来最开始就是realloc出来的
  luaM_free(L, t);
}


static Node *getfreepos (Table *t) {
  while (t->lastfree > t->node) { // 依次从尾向头检查，lastfree 在数组末尾，t->node是数组头
    t->lastfree--;
    if (ttisnil(gkey(t->lastfree)))
      return t->lastfree;
  }
  return NULL;  /* could not find a free place */
}



/*
** inserts a new key into a hash table; first, check whether key's main
** 插入一个新的key到hash表里, 首先检查key的主位置是否为空。如果不为空
** position is free. If not, check whether colliding node is in its main
** position or not: if it is not, move colliding node to an empty place and
** put new key in its main position; otherwise (colliding node is in its main
** position), new key goes to an empty position.
*/
TValue *luaH_newkey (lua_State *L, Table *t, const TValue *key) {
  Node *mp;
  TValue aux;
  // 检查参数，保证key不为空
  if (ttisnil(key)) luaG_runerror(L, "table index is nil");
  // 如果key是float，试着把key转成int。不能转也要保证浮点数不是NaN
  else if (ttisfloat(key)) {
    lua_Integer k;
    if (luaV_tointeger(key, &k, 0)) {  /* index is int? */
      setivalue(&aux, k);
      key = &aux;  /* insert it as an integer */
    }
    else if (luai_numisnan(fltvalue(key)))
      luaG_runerror(L, "table index is NaN");
  }
  mp = mainposition(t, key);
  if (!ttisnil(gval(mp))/*找到的这个hash槽已经被其他占用*/ || isdummy(mp)/*是dummy表示table的hash部分size为空*/) {  /* main position is taken? */
    Node *othern;
    Node *f = getfreepos(t);  /* get a free place */
    if (f == NULL) {  /* cannot find a free place? */ // 从lastfree尾 到 t->node头，全部都被占用了
      rehash(L, t, key);  /* grow table */
      /* whatever called 'newkey' takes care of TM cache */
      return luaH_set(L, t, key);  /* insert key into grown table */
    }
    lua_assert(!isdummy(f)); // isdummy 属于freeplace 不足的情况之一，所以这种情况应该在上面的if里排除了
    // 到了这一步，本来预想的位置已经被mp占了，现在用mp的key来求mod，看看mp是不是在自己的主位置，所谓主位置其实就是key对hashtable的size的求mod就是这个位置
    othern = mainposition(t, gkey(mp));
    if (othern != mp) {  /* is colliding node out of its main position? */
      // 占用点不是mainpoint
      /* yes; move colliding node into free position */
      // 不断先前找知道找到占用点的主位置
      // 已经占用了的位置有一条hash链条,也就是有一串具有相同hash的节点被穿在一起，其中mp是链条中的一条，且不为mainpoint
      // 而 othern 最初是该链中的mainpoint，下面的循环从mainpoint依次轮询，找到mp的前一个点
      while (othern + gnext(othern) != mp)  /* find previous */
        othern += gnext(othern);
      // f是前面找到的空白点，这个时候计算f和othern的偏移，把f这个自由点串在othern后面
      gnext(othern) = cast_int(f - othern);  /* rechain to point to 'f' */
      // 完了把占用点移到这个free点上来
      *f = *mp;  /* copy colliding node into free pos. (mp->next also goes) */
      if (gnext(mp) != 0) {
        // 由于每个节点记录next点采用的都是相对位移，如果占用点mp的next后面还有其他节点，由于现在mp节点已经被copy到free节点了，所以此时还要修正这个free节点的next域指向
        // 不能单纯拷贝占用点mp，由于mp占用点和free节点本身之间也是有偏移的，所以还需要在free节点的next域修正这个偏移
        gnext(f) += cast_int(mp - f);  /* correct 'next' */
        // 完了把占用点next域指向清空，准备给key用
        gnext(mp) = 0;  /* now 'mp' is free */
      }
      setnilvalue(gval(mp));
    }
    else {  /* colliding node is in its own main position */
      // 占用点本身就是主位置
      /* new node will go into free position */
      if (gnext(mp) != 0)
        // (mp + gnext(mp)) - f 是mp节点后面的那个点，这个步骤就是让找到的free点的next域指向这个点
        gnext(f) = cast_int((mp + gnext(mp)) - f);  /* chain new position */
      else lua_assert(gnext(f) == 0);
      // 让mp节点的next域指向free节点
      gnext(mp) = cast_int(f - mp);
      // 修正一下mp指针，这个纯粹是为了让后面统一直接赋值了
      mp = f;
    }
  }
  // 统一赋值，把key的值直接拷贝给找到的mp点
  setnodekey(L, &mp->i_key, key);
  luaC_barrierback(L, t, key);
  lua_assert(ttisnil(gval(mp)));
  return gval(mp);
}


/*
** search function for integers
*/
const TValue *luaH_getint (Table *t, lua_Integer key) {
  /* (1 <= key && key <= t->sizearray) */
  if (l_castS2U(key) - 1 < t->sizearray)
    // 如果key-1在 [0, t->sizearray)区间内，说明存在于table的数组部分，直接从数组部分返回
    return &t->array[key - 1];
  else {
    // 否则就存在于hash部分，先求该key的hash
    Node *n = hashint(t, key);
    for (;;) {  /* check whether 'key' is somewhere in the chain */
      // 从同hash的node链里面找，找到再返回
      if (ttisinteger(gkey(n)) && ivalue(gkey(n)) == key)
        return gval(n);  /* that's it */
      else {
        int nx = gnext(n);
        if (nx == 0) break;
        n += nx;
      }
    }
    // 除了上面的情况外那就是没找到，返回nil
    return luaO_nilobject;
  }
}


/*
** search function for short strings
** 短字符串在同一state只会存在一份，所以比较段字符串的时候直接比较地址
*/
const TValue *luaH_getshortstr (Table *t, TString *key) {
  Node *n = hashstr(t, key);
  lua_assert(key->tt == LUA_TSHRSTR);
  for (;;) {  /* check whether 'key' is somewhere in the chain */
    const TValue *k = gkey(n);
    if (ttisshrstring(k) && eqshrstr(tsvalue(k), key))
      return gval(n);  /* that's it */
    else {
      int nx = gnext(n);
      if (nx == 0) // 除非产生死循环，否则肯定会到0的，这样就是遍历了整个同hash的链，然后没有找到
        return luaO_nilobject;  /* not found */
      n += nx;
    }
  }
}


/*
** "Generic" get version. (Not that generic: not valid for integers,
** which may be in array part, nor for floats with integral values.)
** 通过key从table里获取value的通用方式，通用表示除了整数和可以转换为整数的浮点数以外的key获取value的方式
*/
static const TValue *getgeneric (Table *t, const TValue *key) {
  Node *n = mainposition(t, key);
  for (;;) {  /* check whether 'key' is somewhere in the chain */
    if (luaV_rawequalobj(gkey(n), key))
      return gval(n);  /* that's it */
    else {
      int nx = gnext(n);
      if (nx == 0)
        return luaO_nilobject;  /* not found */
      n += nx;
    }
  }
}


const TValue *luaH_getstr (Table *t, TString *key) {
  if (key->tt == LUA_TSHRSTR)
    return luaH_getshortstr(t, key);
  else {  /* for long strings, use generic case */
    TValue ko;
    // getgeneric只接受TValue参数，把TString转换成TValue
    setsvalue(cast(lua_State *, NULL), &ko, key);
    return getgeneric(t, &ko);
  }
}


/*
** main search function
** 对搜索的优化，主要是对短字符和整数(包括可以转换成整数的浮点数)的查找优化
*/
const TValue *luaH_get (Table *t, const TValue *key) {
  switch (ttype(key)) {
    case LUA_TSHRSTR: return luaH_getshortstr(t, tsvalue(key));
    case LUA_TNUMINT: return luaH_getint(t, ivalue(key));
    case LUA_TNIL: return luaO_nilobject;
    case LUA_TNUMFLT: {
      lua_Integer k;
      if (luaV_tointeger(key, &k, 0)) /* index is int? */
        return luaH_getint(t, k);  /* use specialized version */
      /* else... */
    }  /* FALLTHROUGH */
    default:
      return getgeneric(t, key);
  }
}


/*
** beware: when using this function you probably need to check a GC
** barrier and invalidate the TM cache.
*/
// 返回key的TValue*，没有就造一个
TValue *luaH_set (lua_State *L, Table *t, const TValue *key) {
  const TValue *p = luaH_get(t, key);
  if (p != luaO_nilobject)
    return cast(TValue *, p);
  else return luaH_newkey(L, t, key);
}


// key是一个整数，找到后给其赋值为value
void luaH_setint (lua_State *L, Table *t, lua_Integer key, TValue *value) {
  const TValue *p = luaH_getint(t, key);
  TValue *cell;
  if (p != luaO_nilobject)
    cell = cast(TValue *, p);
  else {
    TValue k;
    setivalue(&k, key);
    cell = luaH_newkey(L, t, &k);
  }
  setobj2t(L, cell, value);
}


static int unbound_search (Table *t, unsigned int j) {
  unsigned int i = j;  /* i is zero or a present index */
  j++; // hash部分整数key是从1开始数的
  /* find 'i' and 'j' such that i is present and j is not */
  while (!ttisnil(luaH_getint(t, j))) { // 每次扩大一倍，直到上界j为nil
    i = j;
    if (j > cast(unsigned int, MAX_INT)/2) {  /* overflow? */
      /* table was built with bad purposes: resort to linear search */
      // 上界炸了，从1开始挨个挨个轮吧。。。
      i = 1;
      while (!ttisnil(luaH_getint(t, i))) i++;
      return i - 1;
    }
    j *= 2;
  }
  /* now do a binary search between them */
  // j为二分查找的上界，i为下界，通过二分查找确定第一个不为nil的边界
  while (j - i > 1) {
    unsigned int m = (i+j)/2;
    if (ttisnil(luaH_getint(t, m))) j = m;
    else i = m;
  }
  return i;
}


/*
** Try to find a boundary in table 't'. A 'boundary' is an integer index
** such that t[i] is non-nil and t[i+1] is nil (and 0 if t[1] is nil).
** 这个应该是在设想某个table都是挨个挨个排队存东西的，中间不存在为nil的node，所以对于这种表只要找到第一个为nil的node，那么ta前一个node的index就是表的长度
*/
int luaH_getn (Table *t) {
  unsigned int j = t->sizearray;
  if (j > 0 && ttisnil(&t->array[j - 1])) {
    /* there is a boundary in the array part: (binary) search for it */
    unsigned int i = 0;
    while (j - i > 1) {
      unsigned int m = (i+j)/2;
      if (ttisnil(&t->array[m - 1])) j = m;
      else i = m;
    }
    return i;
  }
  /* else must find a boundary in hash part */
  else if (isdummy(t->node))  /* hash part is empty? */
    return j;  /* that is easy... */
  else return unbound_search(t, j);
}



#if defined(LUA_DEBUG)

Node *luaH_mainposition (const Table *t, const TValue *key) {
  return mainposition(t, key);
}

int luaH_isdummy (Node *n) { return isdummy(n); }

#endif
