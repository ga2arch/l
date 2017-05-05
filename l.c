#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <sys/mman.h>
#include "l.h"
int debug=1;

//toolkit
I sizes[10] = {sizeof(G*),sizeof(C),sizeof(G),sizeof(H),sizeof(I),sizeof(J),sizeof(E),sizeof(F),sizeof(C),sizeof(S)};
ZI sz(I t) {R sizes[abs(t)];}

// buddy allocator
typedef struct b0 {V* n;G m[0];} *B; //0=free, 1=splitted, 2=full

I md[60000000]={0}; //0=free 1=split 2=full
B lvs[6000]={NULL};
J SIZE=1<<30;

J up2(J v){v--,v|=v>>1,v|=v>>2,v|=v>>4,v|=v>>8,v|=v>>16,v++;R v;}

J blv(L s) {R LOG2(SIZE)-LOG2(up2(s+sizeof(struct b0)));}
L bls(J lv) {R SIZE/(1<<lv);}                                   // buddy level size
L bbi(J lv, G* p) {R (1<<lv)+((G*)p-(G*)lvs[lv])/bls(lv)-1;} // buddy block index
V bi() {lvs[0]=malloc(SIZE),lvs[0]->n=NULL;}                                       // buddy init
V* bal(J lv, L s) {B prev,cur;
  if(lvs[lv]==NULL){lvs[lv]=bal(lv-1,1),lvs[lv]->n=(G*)lvs[lv]+bls(lv);}
  prev=NULL,cur=lvs[lv];
  for(I i=0;i<(1<<lv);i++){L ix;I cs;
    if(cur==NULL) {LO("searching block to split\n");cur=bal(lv-1,1);if(prev!=NULL)prev->n=cur;}
    ix=bbi(lv,cur),cs=md[ix];
    LO("lv:%i - s:%i - ix:%llu\n",lv, cs, ix);
    if(cs==0) {md[ix]=s;LO("found free block\n");R cur->m;};
    if(cs==1||cs==2) prev=cur,cur=cur->n;
  }
  LO("out of memory\n");
  R 0;
}
V* ba(L s) {LO("requested:%i\n",blv(s));V* p=bal(blv(s),2);memset(p,0,s);R p;}            // buddy allocate
V bfree(V* p, L s) {J lv;L ix;
  lv=blv(s),ix=bbi(lv,p),md[ix]=0;
  O("freeing memory: lv:%i, ix:%llu\n",lv,ix);}

ZV* ma(L s) {R ba(s);}
ZV* ra(V* p, L os, L ns) {LO("relloc:<%i,%i>\n",os,ns);G* n=ba(ns);memmove(n,p,os);R n;}
ZK ga(L s) {R ma(sizeof(struct k0)-1+s);}
ZK rga(K x, L n) {R ra(x, sizeof(struct k0)-1+x->n*sz(xt),sizeof(struct k0)-1+sz(xt)*n);}

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
  OS(x);
  I n=xn;
  ixs=ktn(KI,n),bs=ktn(0,10);I bi=0;
  for(;i<n;i++) {
    O("n:%i\n",xn);
    st=state[s][ctype[xG[i]]], s=st.n, e=st.e;
    if (e==EI) {kI(ixs)[ix]=b, kI(ixs)[ix+1]=i-1, b=i, ix+=2;}
    else if (e==EN) b=i;
    LO("i:%i - state: %i - effect:%i - b:%i - ix:%i - c:%c - %i\n", i,s,e,b,ix,xG[i],ctype[xG[i]]);
    if(s==SO&&SEMICOLON==xG[i]){LO("found ; adding block\n");ixs->n=ix;
      ;kK(bs)[bi++]=ixs;DO(ixs->n, LO("%i",kI(ixs)[i]))LO("\n");ixs=ktn(KI,n*2);ix=0;}
  }
  bs->n=bi;
  O("here-%i\n",bs->n);
  OS(x);
  DO(bs->n, K ls=kK(bs)[i];DO(ls->n, LO("<%i>",kI(ls)[i]))LO("\n"););
  R bs;
}

K3(is)   {Os(x);LO(" is %i\n", z->i);R 0;}
K2(plus) {
  LO("<%i,%i>",x->t, y->t);
  if(x->t==-KI&&y->t==-KI)R ki(x->i+y->i);
  else if(x->t==-KI&&y->t==KI){DO(y->n,kI(y)[i]+=x->i);R y;}
  else if(x->t==KI&&y->t==-KI){DO(x->n,kI(x)[i]+=y->i);R x;}
  R 0;}
K2(minus) {I sub=x->i-y->i;LO("sub = %i\n", sub);R ki(sub);}
K2(intf) {LO("intf:%i\n",abs(x->i));K ls=ktn(KI,abs(x->i));I sign=SIGN(x->i);DO(abs(x->i), kI(ls)[i]=(i*sign));R ls;}
K3(dyad) {LO("dyad: %c\n",y->g);PV* v=&pst[y->g];R (*v->f2)(x,z);}
K3(monad) {LO("monad: %c\n",x->g);PV* v=&pst[x->g];R (*v->f1)(z);}

Z C spell[]={
  ':',  ';',  '+', '-',      '!',
  ASGN, MARK, CPLUS, CMINUS, CESCMARK
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

K enqueue(K s, K bs) {K res=ktn(0,10);
  OS(s);
  O("%c\n",kG(s)[0]);
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
    kK(res)[b]=stack[0].e;
  }
  R res;
}

V show(K e) {
  if(e==0) R;
  if(e->t==-KI)O("%i\n", e->i);
  else if(e->t==KI){O("show list of size:%i\n",e->n);DO(e->n,O("%i ", kI(e)[i]));O("\n");};
}

V init() {
  pdef(CPLUS,VERB,0,plus,0,0,0);
  pdef(CMINUS,VERB,0,minus,0,0,0);
  pdef(CESCMARK,VERB,intf,0,0,0,0);

  bi();
}

V repl() {C str[8000]={0};
  O(">> ");
  while(fgets(str,8000,stdin)){K x, rs;
    x=kp(str);x->n--;rs=enqueue(x,wordil(x));
    DO(rs->n, show(kK(rs)[i]));O(">> ");
    bfree(lvs[0],SIZE);
  }
}

I main() {init();repl();
  K x=ktn(0,0);
  jk(&x, kp("ciao"));
  for(I i=0;i<10;i++) {
    K y=ktn(KI,200);
    DO(200, kI(y)[i]=i);
    jk(&x, y);
  }
  for(I i=0;i<10;i++){
    K z=kK(x)[i];
    O("show list of size:%i\n",z->n);DO(z->n,O("%i ", kI(z)[i]));O("\n");
  }

}
