fetch ../tst/prolegomena/appa.tst;

comment | We add a theory of minus -. |
declare funconst -(NATNUM,NATNUM) = NATNUM [inf = 450 455];
deflam minus (N M) (LET ((R (- N M))) (COND ((> R 0) R) (T 0)));
attach - to [NATNUM,NATNUM=NATNUM] minus;
axiom MINUS0R: forall n. n - zro = n;
axiom MINUS0L: forall n. zro - n = zro;
axiom MINUS: forall n m. suc(n) - suc(m) = n - m;
setbasicsimp TMINUS at facts {MINUS0R,MINUS0L,MINUS};

comment | We have some linear equations. |
declare indconst x y z [NATNUM];
axiom Ex: x + suc(suc(zro)) = suc(suc(suc(suc(suc(zro)))));
axiom Ey: y - suc(suc(zro)) = zro;
axiom Ez: z - suc(suc(zro)) = suc(suc(suc(zro)));

comment | Assuming the following theorems, we can solve by hand. |
axiom THM1: forall p q m.(p=q imp p-m=q-m);
comment | NB: The next one is false, because of truncating -. |
axiom THM2: forall p q m.(p+q)-m=p+(q-m);
theorem THM3 PLUS0;

setbasicsimp THM1 at facts {THM1};
setbasicsimp THM2 at facts {THM2};
setbasicsimp THM3 at facts {THM3};

alle THM1 x+suc(suc(zro)),suc(suc(suc(suc(suc(zro))))),suc(suc(zro));
theorem A 1;
rewrite A  by TMINUS uni THM2 uni THM3 uni LOGICTREE;
iffe 2 1;
impe 3 A;
impe 4 Ex;

theorem THMx 5;

comment | Let us switch to the meta level, and do some algebra. |
comment | We will say (not prove) that                          |
comment |     x + n = m is x=m-n (if still non-negative)        |
comment | and x - n = m is x=m+n (always valid).                |
comment | We will require that                                  |
comment | 1. the equation has one of the shapes above,          |
comment | 2. including n and m are literal numbers,             |
comment | 3. for x=m-n we ensure that n<=m.                     |
comment | We will give a solved answer of the form x=n.         |
comment | That is, we do all the checking and computation       |
comment | at the meta level.                                    |
namecontext OBJ;
MAKECONTEXT META;
SWITCHCONTEXT META;

DECLARE PREDCONST THEOREM 1;

DECLARE SORT TERM WFF FACT PREDSYM FUNSYM;

DECREP TERM WFF FACT PREDSYM FUNSYM;
REPRESENT {TERM} AS TERM;
REPRESENT {WFF} AS WFF;
REPRESENT {FACT} AS FACT;
REPRESENT {PREDSYM} AS PREDSYM;
REPRESENT {FUNSYM} AS FUNSYM;

DECLARE FUNCONST wffof (FACT)=WFF;
ATTACH wffof TO [FACT=WFF] fact\-get\-wff;

DECLARE FUNCONST lhs rhs (WFF)=TERM;
DECLARE FUNCONST larg rarg (TERM)=TERM;
ATTACH lhs TO [WFF=TERM] lhs;
ATTACH rhs TO [WFF=TERM] rhs;
DEFLAM larg (t) (CAR (appl\-get\-args t));
ATTACH larg TO [TERM=TERM] larg;
DEFLAM rarg (t) (CADR (appl\-get\-args t));
ATTACH rarg TO [TERM=TERM] rarg;

DECLARE FUNCONST mainpred (WFF)=PREDSYM;
DECLARE FUNCONST pred2apply (PREDSYM TERM TERM)=WFF;
DECLARE INDCONST Equal [PREDSYM];
MATTACH Equal dar [PREDSYM] OBJ::PREDCONST:=;
DEFLAM mainpred (X) (AND (PREDAPPL X) (predappl\-get\-pred X));
ATTACH mainpred to [WFF=PREDSYM] mainpred;
ATTACH pred2apply TO [PREDSYM,TERM,TERM=WFF] predappl2\-mak;

DECLARE FUNCONST mainfun (TERM)=FUNSYM;
DECLARE FUNCONST fun1apply (FUNSYM TERM)=TERM;
DECLARE FUNCONST fun2apply (FUNSYM TERM TERM)=TERM;
DECLARE INDCONST zro [TERM];
DECLARE INDCONST suc + - [FUNSYM];
MATTACH zro dar [TERM] OBJ::INDCONST:zro;
MATTACH suc dar [FUNSYM] OBJ::FUNCONST:suc;
MATTACH + dar [FUNSYM] OBJ::FUNCONST:+;
MATTACH - dar [FUNSYM] OBJ::FUNCONST:-;
DEFLAM mainfun (X) (AND (FUNAPPL X) (funappl\-get\-fun X));
ATTACH mainfun to [TERM=FUNSYM] mainfun;
ATTACH fun1apply TO [FUNSYM,TERM=TERM] funappl1\-mak;
ATTACH fun2apply TO [FUNSYM,TERM,TERM=TERM] funappl2\-mak;

DECLARE indvar x y z [TERM];
DECLARE indvar w [WFF];
DECLARE indvar vl [FACT];

DECLARE PREDCONST NUMERAL 1;
DECLARE PREDCONST numeral 3;
DEFLAM numeral (X zro suc) (OR (EQ X zro) (AND (FUNAPPL X) (EQ (funappl\-get\-fun X) suc) (numeral (funappl1\-get\-arg X) zro suc)));
ATTACH numeral TO [TERM,TERM,FUNSYM] numeral;
AXIOM AX_NUMERAL: forall x.(NUMERAL(x) iff numeral(x,zro,suc));

KNOW natnums;
declare indvar n [NATNUMSORT];
DECLARE FUNCONST mknum (TERM)=NATNUMSORT;
DEFLAM mknum (X) (IF (FUNAPPL X) (ADD1 (mknum (funappl1\-get\-arg X))) 0);
ATTACH mknum TO [TERM=NATNUMREP] mknum;
DECLARE FUNCONST mknumerali (NATNUMSORT,TERM,FUNSYM)=TERM;
DECLARE FUNCONST mknumeral (NATNUMSORT)=TERM;
DEFLAM mknumerali (X zro suc) (IF (= X 0) zro (funappl1\-mak suc (mknumerali (SUB1 X) zro suc)));
ATTACH mknumerali TO [NATNUMREP,TERM,FUNSYM=TERM] mknumerali;
AXIOM AX_MKNUMERAL: forall n.(mknumeral(n)=mknumerali(n,zro,suc));

DECLARE PREDCONST LEQ 2;
DEFLAM leq (X Y) (OR (< X Y) (= X Y));
ATTACH LEQ TO [NATNUMREP,NATNUMREP] leq;

DECLARE FUNCONST plus minus (NATNUMSORT NATNUMSORT)=NATNUMSORT;
ATTACH plus TO [NATNUMREP,NATNUMREP=NATNUMREP] +;
ATTACH minus TO [NATNUMREP,NATNUMREP=NATNUMREP] -;

DECLARE FUNCONST mkequal (TERM TERM)=WFF;
AXIOM AX_MKEQUAL: forall x y.mkequal(x,y)=pred2apply(Equal,x,y);

DECLARE PREDCONST LINEAREQ 2;
DECLARE FUNCONST solve (WFF TERM)=TERM;

comment | The 3 next axioms are close to the formulation in the paper. |

AXIOM AX_LINEAREQ: forall w x.(LINEAREQ(w,x) iff (
  mainpred(w)=Equal and
  (mainfun(lhs(w))=+ or mainfun(lhs(w))=-) and
  larg(lhs(w))=x and
  (NUMERAL(rarg(lhs(w))) and NUMERAL(rhs(w))) and
  (mainfun(lhs(w))=+ imp LEQ(mknum(larg(lhs(w))),mknum(rhs(w))))));

AXIOM AX_SOLVE: forall w x.(solve(w, x)=
  trmif mainfun(lhs(w))=+
  then mknumeral(minus(mknum(rhs(w)),mknum(rarg(lhs(w)))))
  else mknumeral(plus(mknum(rhs(w)),mknum(rarg(lhs(w))))));

AXIOM SOLVE: forall vl x.(LINEAREQ(wffof(vl),x) imp THEOREM(mkequal(x,solve(wffof(vl),x))));

SETBASICSIMP meta\-axioms at facts {AX_LINEAREQ,AX_SOLVE,AX_NUMERAL,AX_MKNUMERAL,AX_MKEQUAL};
SETCOMPSIMP EVALSS AT LOGICTREE uni meta\-axioms;

SWITCHCONTEXT OBJ;

reflect SOLVE Ey y;
theorem THMy 6;

reflect SOLVE Ex x;
theorem THx2 7;

reflect SOLVE Ez z;
theorem THMz 8;

show axiom;
