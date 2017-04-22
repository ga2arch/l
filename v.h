#define DO(n,x)	{J i=0,_i=(n);for(;i<_i;++i){x;}}
#define O printf
#define OS(s) DO(s->n, O("%c",kG(s)[i]))O("\n");
#define Os(s) DO(s->n, O("%c",kG(s)[i]));
#define R return
#define Z static
#define P(x,y) {if(x)R(y);}
#define U(x) P(!(x),0)
#define $(x,y,z) {if(x){y;}else{z;}}
#define SW switch
#define CD default
#define CS(n,x)	case n:x;break;

#define ZV Z V
#define ZK Z K
#define ZH Z H
#define ZI Z I
#define ZJ Z J
#define ZE Z E
#define ZF Z F
#define ZC Z C
#define ZS Z S

// alias
typedef char*S,C;
typedef unsigned char G;
typedef short H;
typedef int I;
typedef long long J;
typedef float E;
typedef double F;
typedef void V;

// types
#define KB 1  // 1 boolean   char   kG
#define KG 2  // 1 byte      char   kG
#define KH 3  // 2 short     short  kH
#define KI 4  // 4 int       int    kI
#define KJ 5  // 8 long      long   kJ
#define KE 6  // 4 real      float  kE
#define KF 7  // 8 float     double kF
#define KC 8  // 1 char      char   kC
#define KS 9  // * symbol    char*  kS

// accessors
#define K1(f) K f(K x)
#define K2(f) K f(K x,K y)
#define K3(f) K f(K x,K y,K z)
#define TX(T,x) (*(T*)((G*)(x)+8))
#define xr x->r
#define xt x->t
#define xu x->u
#define xn x->n
#define xx xK[0]
#define xy xK[1]
#define xg TX(G,x)
#define xh TX(H,x)
#define xi TX(I,x)
#define xj TX(J,x)
#define xe TX(E,x)
#define xf TX(F,x)
#define xs TX(S,x)
#define xk TX(K,x)
#define xG x->G0
#define xH ((H*)xG)
#define xI ((I*)xG)
#define xJ ((J*)xG)
#define xE ((E*)xG)
#define xF ((F*)xG)
#define xS ((S*)xG)
#define xK ((K*)xG)
#define xC xG
#define xB ((G*)xG)

#define kG(x)	((x)->G0)
#define kC(x)	kG(x)
#define kH(x)	((H*)kG(x))
#define kI(x)	((I*)kG(x))
#define kJ(x)	((J*)kG(x))
#define kE(x)	((E*)kG(x))
#define kF(x)	((F*)kG(x))
#define kS(x)	((S*)kG(x))
#define kK(x)	((K*)kG(x))

// type
typedef struct k0{
  signed char t;
  union{G g;H h;I i;J j;E e;F f;S s;struct k0*k;struct{J n;G G0[1];};};
}*K;
/* t: id of the type
   n: number of atoms */

//

#define ANY     -1L
#define VERB    (I)1L
#define ADV     (I)2L
#define NAME    (I)8L
#define CHAR    (I)16L
#define INT     (I)32L
#define MARK    (I)64L


#define VNA     (VERB+NOUN+ADV)
#define EDGE    (MARK+ASGN)
#define NUMERIC (INT)
#define NOUN    (NUMERIC+CHAR)

#define ASGN    '\200'
#define CPLUS    '+'
#define CMINUS   '-'

typedef struct {C v; K(*Kf);} VB;
typedef struct {I c[4]; K(*f)(K,K,K); I b,e;} PT;
typedef struct {I t; K e;} SQ;
typedef struct {K(*f1)(K); K(*f2)(K,K); I t; I mr; I lr; I rr; C id;} PV;
