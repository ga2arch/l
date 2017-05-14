#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <math.h>
#include "l.h"
int debug=0;

//buddy
#define LV(s,ts)      (LOG2(ts/np2((s))))
#define BL(lv)        (1<<(lv))
#define SLV(lv,ts)    ((ts)/BL(lv))
#define IX(p,lv,m,ts) (((p)-(m))/(SLV(lv,ts)))

typedef struct b0 {struct b0* n;} *B;
typedef struct bl0 {struct bl0* p;struct bl0* n;} *BL;
L SIZE=(1UL<<20)*2; // 1mb
V* mem;
V* lvs[32]={NULL};
B* bs[32]={NULL};

ZL np2(L v){v--;v|=v>>1;v|=v>>2;v|=v>>4;v|=v>>8;v|=v>>16;v|=v>>32;v++;R v;}
ZV binit() {posix_memalign(&mem,16,SIZE);memset(mem,0,SIZE);lvs[0]=mem,((BL)lvs[0])->p=((BL)lvs[0])->n=NULL;}
ZV* bal(L lv) {BL bl;
  if(lv==0&&lvs[lv]==NULL){O("out of memory\n");R 0;}
  if(lvs[lv]==NULL) {V* m;BL r;m=bal(lv-1),r=m+SLV(lv,SIZE);r->n=r->p=NULL,lvs[lv]=r;R m;}
  bl=(BL)lvs[lv];
  LO("allocate: lv:%llu - ix:%llu\n",lv,IX((V*)bl,lv,mem,SIZE));
  if(bl->n)lvs[lv]=bl->n,((BL)lvs[lv])->p=NULL;
  else lvs[lv]=NULL;
  R bl;
}
ZV* ba(L s) {LO("requested:%llu - %llu\n",s,LV(s,SIZE));R bal(LV(s,SIZE));}
ZV bfl(V* p,L lv) {L ix,size;G* buddy;BL tmp,bl;I found=0;
  ix=IX(p,lv,mem,SIZE),size=SLV(lv,SIZE);
  LO("freeing lv:%llu - ix:%llu - p:%p\n",lv,ix,p);
  $((ix&1)==0, buddy=(G*)p+size, buddy=(G*)p-size);tmp=lvs[lv];
  while(tmp) {found=(G*)tmp==buddy;if(tmp->n==NULL)break;tmp=tmp->n;}
  if(found) {O("found buddy\n");BL prev,next;
    bl=(BL)buddy,prev=bl->p,next=bl->n;
    if(prev) prev->n=next;if(next) next->p=prev;
    $((ix&1)==0,bfl(p, lv-1),bfl(buddy,lv-1));R;}
  bl=(BL)p,bl->p=tmp,bl->n=NULL;
  $(tmp, tmp->n=p, tmp=p)
  lvs[lv]=tmp;
}
ZV bf(V* p,L s) {bfl(p,LV(s,SIZE));}

//toolkit
I sizes[10] = {sizeof(G*),sizeof(C),sizeof(G),sizeof(H),sizeof(I),sizeof(J),sizeof(E),sizeof(F),sizeof(C),sizeof(S)};
ZI sz(I t) {R sizes[abs(t)];}

/* ZV* ma(L s) {V* v=malloc(s);memset(v,0,s);R v;} */
/* ZV* ra(V* p, L os, L ns) {R realloc(p, ns);} */

ZV* ma(L s) {V* v=ba(s);memset(v,0,s);R v;}
ZV* ra(V* p, L os, L ns) {V* n=ma(ns);memmove(n,p,os);bf(p,os);R n;}

ZK ga(L s) {R ma(sizeof(struct k0)-1+s);}
ZK rga(K x, L n) {R ra(x, sizeof(struct k0)-1+xn*sz(xt),sizeof(struct k0)-1+sz(xt)*n);}
ZV gf(K x) {L s=sizeof(struct k0);if(xt<1)s+=-1+xn*sz(xt);bf(x,s);}

// atoms
ZK ka(I t) {K x=ga(0);xt=t;R x;}
ZK kc(C c) {K x=ka(-KC);x->g=(G)c;R x;}
ZK ki(I i) {K x=ka(-KI);x->i=i;R x;}

// lists
ZK ktn(I t, L n) {K x;U(t>=0&&t<10);x=ga(sz(t)*n);xt=t,xn=n;R x;};
ZK kpn(S s, I n) {K x=ktn(KC,n);memcpy((S)xG,s,n);R x;}
ZK kp(S s) {R kpn(s,strlen(s));}
ZK ja(K* x, V* y) {*x=rga(*x,(*x)->n+1);memcpy(&kK(*x)[(*x)->n],y,sz((*x)->t));(*x)->n++;R *x;}
ZK js(K* x, S s) {I n=strlen(s);*x=rga(*x,(*x)->n+n);memcpy(&kG(*x)[(*x)->n],s,n);(*x)->n+=n;R *x;}
ZK jk(K* x, K y) {*x=rga(*x,(*x)->n+1);memcpy(&kK(*x)[(*x)->n],&y,sizeof(G*));(*x)->n++;R *x;}
ZK jv(K* x, K y) {U((*x)->t==y->t);I n=(*x)->n;*x=rga(*x,n+y->n);memcpy(&kK(*x)[n],&kG(y),y->n*sz(y->t));(*x)->n=n+y->n;R *x;}

//tables


//parser
#define SB         0    /* blank                           */
#define SA         1    /* alphanumeric                    */
#define SO         2    /* other                           */
#define S9         3    /* digit                           */

#define EI         1    /* emit (b,i-1); b=.i              */
#define EN         2    /* b=.i                            */

#define CO         0    /* other                           */
#define CB         1    /* space or tab                    */
#define CA         2    /* letter                          */
#define C9         3    /* digit */
#define CC         4    /* colon */
#define CQ         5    /* quote */

typedef struct {C n,e;} ST;

Z ST state[4][4]={
  /*SB */ {{SO,EN},{SB,0 },{SA,EN},{S9,EN}},
  /*SA */ {{SO,EI},{SB,EI},{SA,0 },{S9,EI}},
  /*SO */ {{SO,EI},{SB,EI},{SA,EI},{S9,EI}},
  /*S9 */ {{SO,EI},{SB,EI},{SA,EI},{S9,0}},
};
/*          CO      CB      CA      C9   */

C ctype[256]={
 0,  0,  0,  0,  0,  0,  0,  0,  0, CB,  0,  0,  0,  0,  0,  0, /* 0                  */
 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0, /* 1                  */
CB,  0,  0,  0,  0,  0,  0, CQ,  0,  0,  0,  0,  0,  0,  0,  0, /* 2  !"#$%&'()*+,-./ */
C9, C9, C9, C9, C9, C9, C9, C9, C9, C9, CO,  0,  0,  0,  0,  0, /* 3 0123456789:;<=>? */
 0, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, /* 4 @ABCDEFGHIJKLMNO */
CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA,  0,  0,  0,  0, C9, /* 5 PQRSTUVWXYZ[\]^_ */
 0, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, /* 6 `abcdefghijklmno */
CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA,  0,  0,  0,  0,  0, /* 7 pqrstuvwxyz{|}~  */
};

PV pst[256]={0};
I ttype[] = {0,0,0,0,INT,0,0,0,0,CHAR};
ZI pt(I t) {R ttype[abs(t)];}

K wordil(K x) {I i=0,s=0,e=0,b=0,ix=0;ST st;K ixs;K bs;
  ixs=ktn(KI,xn*2),bs=ktn(0,0);
  for(;i<xn;i++) {
    st=state[s][ctype[xG[i]]], s=st.n, e=st.e;
    if (e==EI) {kI(ixs)[ix]=b, kI(ixs)[ix+1]=i-1, b=i, ix+=2;}
    else if (e==EN) b=i;
    LO("i:%i - state: %i - effect:%i - b:%i - ix:%i - c:%c - %i\n",i,s,e,b,ix,xG[i],ctype[xG[i]]);
    if(s==SO&&SEMICOLON==xG[i]){LO("found ; adding block\n");ixs->n=ix;jk(&bs,ixs);ixs=ktn(KI,xn*2);ix=0;}
  }
  R bs;
}

#define V1M(name, op, XTYPE, ZTYPE, rt) K1(name) {K z;J size=sz(K ## XTYPE);  \
    if(x->t==-K ## XTYPE)R rt(op(*(XTYPE*)((G*)x+8))); \
    if(x->t==K ## XTYPE){z=ktn(K ## ZTYPE,x->n); \
      DO(x->n,*(ZTYPE*)(((G*)z)+16+size*i)=op(*(XTYPE*)(((G*)x)+16+size*i)));R z;} \
    R 0;                                                                \
}
#define V1F(name, op, XTYPE, ZTYPE, rt) K1(name) {K z; op;R z;}
#define V2(name, op, XTYPE, YTYPE, ZTYPE, rt) K2(name) {K z; \
    if(x->t==-K ## XTYPE&&y->t==-K ## YTYPE)R rt(*(XTYPE*)((G*)x+8) op *(XTYPE*)((G*)y+8)); \
    if(x->t==-K ## XTYPE&&y->t==K ## YTYPE){z=ktn(K ## ZTYPE,y->n); \
      DO(y->n,*(ZTYPE*)(((G*)z)+16+sz(K ## XTYPE)*i)=*(YTYPE*)(((G*)y)+16+sz(K ## XTYPE)*i) op *(XTYPE*)(((G*)x)+8));R z;} \
    if(x->t==K ## XTYPE&&y->t==-K ## YTYPE){z=ktn(K ## ZTYPE,x->n); \
      DO(x->n,*(ZTYPE*)(((G*)z)+16+sz(K ## XTYPE)*i)=*(XTYPE*)(((G*)x)+16+sz(K ## XTYPE)*i) op *(YTYPE*)(((G*)y)+8));R z;} \
    R 0;                                                                \
}

Z inline I neg(I i) {R -i;}

V1M(absoluteII,llabs,I,I,ki)
V1M(negateII,neg,I,I,ki)
V1F(headII,{$(xt>0, z=ki(kI(x)[0]), z=ki(x->i))},I,I,ki)

V2(plusIII,+,I,I,I,ki)
V2(minusIII,-,I,I,I,ki)
V2(mulIII,*,I,I,I,ki)

K2(plus)  {P(abs(xt)==KI&&abs(y->t)==KI, plusIII(x,y));}
K2(minus) {P(abs(xt)==KI&&abs(y->t)==KI, minusIII(x,y));}
K2(mul)   {P(abs(xt)==KI&&abs(y->t)==KI, mulIII(x,y));}

K2(absolute) {P(abs(xt)==KI, absoluteII(x));}
K2(negate) {P(abs(xt)==KI, negateII(x));}
K2(mul1) {P(abs(xt)==KI, headII(x));}

K2(intf) {LO("intf:%i\n",abs(x->i));K ls=ktn(KI,abs(x->i));I sign=SIGN(x->i);DO(abs(x->i), kI(ls)[i]=(i*sign));R ls;}
K3(dyad) {LO("dyad: %c\n",y->g);PV* v=&pst[y->g];R (*v->f2)(x,z);}
K3(monad) {LO("monad: %c\n",x->g);PV* v=&pst[x->g];R (*v->f1)(z);}
K3(is)   {Os(x);LO(" is %i\n", z->i);R 0;}

Z C spell[]={
  ':',  ';',  '+',   '-',    '!',      '*',
  ASGN, MARK, CPLUS, CMINUS, CESCMARK, CMUL
};
C spellin(C c) {DO(sizeof(spell)/2,P(spell[i]==c,spell[i+(sizeof(spell)/2)]));R 0;}
I ds(G id) {DO(sizeof(ctype), P(pst[id].id==id, pst[id].t));R 0;}
I qn(S tk, L n) {DO(n, P(tk[i]<'0'||(tk[i]>'9'&&tk[i]<'A')||(tk[i]>'Z'&&tk[i]<'a')||tk[i]>'z',0));R NOUN;}
I qv(C c) {I s;I ct;s=spellin(c);U(ct=ds(s));R ct;}
ZI pdef(C id, I t, K(*f1)(), K(*f2)(), I mr, I lr, I rr) {PV* v=&pst[(G)id];v->id=id,v->f1=f1,v->f2=f2,v->mr=mr,v->lr=lr,v->rr=rr,v->t=t;R 1;}

PT cases[] = {
  NOUN+NAME, ASGN,       VNA,  ANY,  is,    0, 2,
  MARK,      NOUN+NAME,  ASGN, VNA,  is,    1, 3,
  EDGE+VNA,  NOUN,       VERB, NOUN, dyad,  1, 3,
  EDGE+VNA,  VERB,       NOUN, ANY,  monad, 1, 2,
  EDGE+VNA,  ANY,        VERB, NOUN, monad, 2, 3
};

K enqueue(K s, K bs) {K res=ktn(0,0);
  DO(bs->n, K ixs=kK(bs)[i];DO(ixs->n, LO("%i",kI(ixs)[i]))LO("\n"););
  for(I b=0;b<bs->n;b++) {I top=0;SQ stack[8000]={0};K ixs=kK(bs)[b];
    for(I i=ixs->n-1;i>=0;i-=2) {S tk;L len=0;K r;I ct=-1, ws=4, ret=0;
      tk=(S)kC(s)+kI(ixs)[i-1], len=kI(ixs)[i]-kI(ixs)[i-1]+1, ct=ctype[tk[0]];
      LO("\nt: %i", ct);
      SW(ct) {
        CS(CO, {if((ct=qv(tk[0]))==0)ct=spellin(tk[0]);r=kc(tk[0]);})
        CS(CA, (ct=CHAR,    r=kpn(tk, len)))
        CS(C9, (ct=NUMERIC, r=ki(atoi(tk))))
        CD:    (ct=NOUN,    r=kpn(tk, len));
      }
      LO("\n");
      DO(len, LO("<%c,%i>", tk[i], r->i););
      LO(" - %i", ct);LO("\n");
      stack[top].t=ct, stack[top].e=r, top+=1;
      LO("top: %i", top);LO("\n");
      DO(top, LO("<%i,%i> - ", stack[i].t, stack[i].e->i))LO("\n");
      if(top<4&&i>1)continue;
      if(top<4)for(;top<4;top++)stack[top].t=MARK,stack[top].e=kp(";");
      DO(top, LO("<%i,%i> - ", stack[i].t, stack[i].e->i))LO("\n");
      do {
        for(I j=0;j<sizeof(cases)/sizeof(cases[0]);j++) {I cond=1;I start;I off;
          start=top-ws, off=ws-1;
          DO(ws, cond=cond&&(cases[j].c[i]&stack[start+off-i].t));
          if (cond) {I a,b,o=0;
            a=cases[j].b, b=cases[j].e;
            r=(*cases[j].f)(stack[start+off-a].e,stack[start+off-a-1].e,stack[start+off-b].e);
            if(r)stack[start+off-b].t=pt(r->t), stack[start+off-b].e=r, o=1;
            memmove(&stack[start+off-b+o], &stack[start+off-a+1], (top-a)*sizeof(stack[0]));
            top-=b-a+(o?0:1), ret=1;
            break;
          }
          ret=0;
        }
        if(ret&&i==1)for(;top<4;top++)stack[top].t=MARK,stack[top].e=kp(";");
      } while (i==1&&ret);
    }
    gf(ixs);
    jk(&res,stack[0].e);
  }
  gf(s);
  R res;
}

V show(K e) {
  if(e==0) R;
  if(e->t==-KI)O("%i\n", e->i);
  else if(e->t==KI){LO("show list of size:%llu\n",e->n);DO(e->n,O("%i ", kI(e)[i]));O("\n");};
}

V init() {
  pdef(CPLUS,VERB,absolute,plus,0,0,0);
  pdef(CMINUS,VERB,negate,minus,0,0,0);
  pdef(CMUL,VERB,mul1,mul,0,0,0);
  pdef(CESCMARK,VERB,intf,0,0,0,0);

  binit();
  O("allocated %llu\n",SIZE);
}

V repl() {C str[8000]={0};
  O(">> ");
  while(fgets(str,8000,stdin)){K x, rs;
    x=kp(str);x->n--;js(&x,";");rs=enqueue(x,wordil(x));
    DO(rs->n, show(kK(rs)[i]));O(">> ");
    gf(rs);
  }
}

I main() {init();repl();
  K y=ktn(0,0);
  K z=ktn(KI,20000);
  jk(&y,z);
  DO(2000, kI(kK(y)[0])[i]=i);
  LO("show list of size:%llu\n",2000);DO(2000,O("%i ", kI(kK(y)[0])[i]));O("\n");

}
