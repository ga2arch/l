#include "v.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#define SB         0    /* blank                           */
#define SA         1    /* alphanumeric                    */
#define SO         2    /* other                           */

#define EI         1    /* emit (b,i-1); b=.i              */
#define EN         2    /* b=.i                            */

#define CB         0    /* space or tab                    */
#define CA         1    /* letter                          */
#define CO         2    /* other                           */

typedef struct {C n,e;} ST;

Z ST state[3][3]={
  /*SB */ {{SB,0 },{SA,EN},{SO,EN}},
  /*SA */ {{SB,EI},{SA,0 },{SO,EI}},
  /*SO */ {{SB,EI},{SA,EI},{SO,EN}}
};
/*          CB      CA     CO     */

PV pst[256]={};
I ctype(C c) {
  P(c==' '||c=='\t', CB)
  P(c==';'||c==':'||c=='+',  CO)
  R CA;
}

ZV* ma(J s) {V* p=malloc(s);memset(p,0,s);R p;}
ZK ga(J s) {R ma(sizeof(struct k0)-1+s);}
ZK ktn(I t, J n) {I s=0;K x;U(t>0&&t<10);
  SW(t) {
      CS(KB, s=sizeof(C))
      CS(KG, s=sizeof(C))
      CS(KH, s=sizeof(H))
      CS(KI, s=sizeof(I))
      CS(KJ, s=sizeof(J))
      CS(KE, s=sizeof(E))
      CS(KF, s=sizeof(F))
      CS(KC, s=sizeof(C))
      CS(KS, s=sizeof(S))
  }
  x=ga(s*n), xt=t, xn=n;
  R x;
}
ZK ks(S s) {I n=strlen(s);K x=ktn(KC,n);strncpy((S)xG,s,n);R x;}
ZK kc(C c) {K x=ga(0);x->t=KC, x->g=(G)c;R x;}
ZK ki(I i) {K x=ga(0);x->t=KI, x->i=i;R x;}
ZK ksn(S s, I n) {K x=ktn(KC,n);strncpy((S)xG,s,n);R x;}

K1(wordil) {I i=0,s=0,e=0,b=0,wi=0;ST st;K w=ktn(KI,xn*2);
  for(;i<xn;i++) {
    O("i:%i - state: %i - effect:%i - b:%i - wi:%i\n", i,s,e,b,wi);
    st=state[s][ctype(xG[i])], s=st.n, e=st.e;
    if (e==1) {kI(w)[wi]=b, kI(w)[wi+1]=i-1, b=i, wi+=2;}
    else if (e==2) {b=i;}
  }
  kI(w)[wi]=b, kI(w)[wi+1]=i-1, w->n=wi+2;
  R w;
}

K3(is)   {O("is\n");Os(x);O(" is %i\n", z->i);R ki(0);}
K2(plus) {I a=0,b=0;
  $(x->t==KC, a=atoi((S)xG), a=x->i);
  $(y->t==KC, b=atoi((S)kG(y)), b=y->i);
  I sum=a+b;O("sum = %i\n", sum);R ki(sum);
}
K3(dyad) {PV* v=&pst[y->g]; R (*v->f2)(x,z);}

I qn(S tk, J n) {
  DO(n, P(tk[i]<'0'||(tk[i]>'9'&&tk[i]<'A')||(tk[i]>'Z'&&tk[i]<'a')||tk[i]>'z',0));
  R NOUN;
}
I qv(S tk) {R 0;}

ZI pdef(C id, I t, K(*f1)(), K(*f2)(), I mr, I lr, I rr) {
  PV* v=&pst[(G)id];
  v->id=id;
  v->f1=f1;
  v->f2=f2;
  v->mr=mr;
  v->lr=lr;
  v->rr=rr;
  v->t=t;
  R 1;
}

Z C spell[2][3]={
  ':',  ';',  '+',
  ASGN, MARK, CPLUS
};
I spellin(C c) {DO(sizeof(spell), P(spell[0][i]==c,spell[1][i]));R 0;}

PT cases[] = {
  NOUN+NAME, ASGN,       VNA,  ANY,  is,   0, 2,
  MARK,      NOUN+NAME,  ASGN, VNA,  is,   1, 3,
  EDGE+VNA,  NOUN,       VERB, NOUN, dyad, 1, 3
};

V enqueue(K s, K w) {
  O("\n");
  I top=0;SQ stack[8000]={};

  for(I i=w->n-1;i>=0;i-=2) {
    S tk; J len=0; I type=0; K r;
    tk=(S)kC(s)+kI(w)[i-1], len=kI(w)[i]-kI(w)[i-1]+1;
    (type=qn(tk,len))?type:(type=qv(tk))?type:(type=spellin(tk[0]))?type:(type=0);

    if (tk[0]==':')type=ASGN;
    if (tk[0]==';')type=MARK;
    if (tk[0]=='+')type=CPLUS;

    O("\n");
    DO(len, O("%c", tk[i]););
    O(" - %i", type);O("\n");

    stack[top].t=type, stack[top].e=ksn(tk,len), top+=1;
    if(type==CPLUS) {PV*v=&pst[(G) type]; stack[top-1].t=v->t, stack[top-1].e=kc(v->id);}

    O("top: %i", top);O("\n");
    DO(top, O("%i - ", stack[i].t))O("\n");
    if(top<4)continue;

    for(I j=0;j<sizeof(cases)/sizeof(cases[0]);j++) {I cond=1;I start;
      start=top-4;
      DO(4, cond=cond&&(cases[j].c[i]&stack[start+3-i].t));

      if (cond) {I a,b;
        a=cases[j].b, b=cases[j].e;
        r=(*cases[j].f)(stack[start+3-a].e,stack[start+3-a-1].e,stack[start+3-b].e);

        stack[start+3-b].t=NOUN;
        stack[start+3-b].e=r;
        memmove(&stack[start+3-b+1], &stack[start+3-a+1], top-(start+3-a+1));
        top-=b-a;
        break;
      }
    }
  }
  free(w);
  free(s);
}

int main() {
  pdef(CPLUS,VERB,0,plus,0,0,0);

  K x=ks("y:1;x:2+10+10");

  K w=wordil(x);
  O("%lld\n", w->n);
  DO(w->n, O("%i",kI(w)[i]));
  O("\n");
  enqueue(x,w);

}
