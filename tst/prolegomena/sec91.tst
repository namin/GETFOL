fetch ../tst/prolegomena/appa.tst;

declare indconst x y z [NATNUM];
axiom E: x + suc(suc(zro)) = suc(suc(suc(suc(suc(zro)))));

declare funconst -(NATNUM,NATNUM) = NATNUM [inf = 450 455];
deflam minus (N M) (LET ((R (- N M))) (COND ((> R 0) R) (T 0)));
attach - to [NATNUM,NATNUM=NATNUM] minus;
axiom MINUS0R: forall n. n - zro = n;
axiom MINUS0L: forall n. zro - n = zro;
axiom MINUS: forall n m. suc(n) - suc(m) = n - m;
setbasicsimp TMINUS at facts {MINUS0R,MINUS0L,MINUS};

axiom THM1: forall p q m.(p=q imp p-m=q-m);
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
impe 4 E;

theorem THMx 5;

namecontext OBJ;
MAKECONTEXT META;
SWITCHCONTEXT META;

DECLARE PREDCONST THEOREM 1;

DECLARE SORT TERM WFF PREDSYM FUNSYM;

DECREP TERM WFF PREDSYM FUNSYM;
REPRESENT {TERM} AS TERM;
REPRESENT {WFF} AS WFF;
REPRESENT {PREDSYM} AS PREDSYM;
REPRESENT {FUNSYM} AS FUNSYM;

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
DECLARE indvar op [FUNSYM];

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

DECLARE PREDCONST SOLVE_THM LINEAREQ 2;
DECLARE FUNCONST solve (WFF TERM)=TERM;
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

AXIOM AX_SOLVE_THM: forall w x.(SOLVE_THM(w,x) iff (LINEAREQ(w,x) imp THEOREM(pred2apply(Equal,x,solve(w,x)))));

AXIOM SOLVE: forall w x.SOLVE_THM(w,x);

AXIOM SOLVE_MINUS_LINEAREQ: forall x y z.SOLVE_THM(pred2apply(Equal,fun2apply(-,x,y),z),x);

SETBASICSIMP meta\-axioms at facts {AX_LINEAREQ,AX_SOLVE,AX_SOLVE_THM,AX_NUMERAL,AX_MKNUMERAL};
SETCOMPSIMP EVALSS AT LOGICTREE uni meta\-axioms;

SWITCHCONTEXT OBJ;

reflect SOLVE (y-suc(suc(zro))=zro) y;
theorem THMy 6;

reflect SOLVE (x+suc(suc(zro))=suc(suc(suc(suc(suc(zro)))))) x;
theorem THx2 7;

reflect SOLVE_MINUS_LINEAREQ z suc(suc(zro)) suc(suc(suc(zro)));
theorem THMz 8;

show axiom;
