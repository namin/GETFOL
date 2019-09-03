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

DECLARE SORT TERM WFF FACT PREDCONST FUNCONST INDCONST;

DECREP TERM WFF FACT PREDCONST FUNCONST INDCONST;
REPRESENT {TERM} AS TERM;
REPRESENT {WFF} AS WFF;
REPRESENT {FACT} AS FACT;
REPRESENT {PREDCONST} AS PREDCONST;
REPRESENT {FUNCONST} AS FUNCONST;
REPRESENT {INDCONST} AS INDCONST;

MOREGENERAL TERM <INDCONST>;

DECLARE FUNCONST wffof (FACT)=WFF;
DECLARE FUNCONST lhs rhs (WFF)=TERM;
DECLARE FUNCONST larg rarg (TERM)=TERM;
ATTACH wffof TO [FACT=WFF] fact\-get\-wff;
ATTACH lhs TO [WFF=TERM] lhs;
ATTACH rhs TO [WFF=TERM] rhs;
DEFLAM larg (t) (CAR (appl\-get\-args t));
ATTACH larg TO [TERM=TERM] larg;
DEFLAM rarg (t) (CADR (appl\-get\-args t));
ATTACH rarg TO [TERM=TERM] rarg;

DECLARE FUNCONST mkimp (WFF WFF)=WFF;
ATTACH mkimp TO [WFF,WFF=WFF] mkimp;
DECLARE FUNCONST mkand (WFF WFF)=WFF;
ATTACH mkand TO [WFF,WFF=WFF] mkand;
DECLARE FUNCONST mktrmif (WFF TERM TERM)=TERM;
ATTACH mktrmif TO [WFF,TERM,TERM=TERM] mktrmif;

DECLARE FUNCONST pred1apply (PREDCONST TERM)=WFF;
DECLARE FUNCONST pred2apply (PREDCONST TERM TERM)=WFF;
DECLARE INDCONST Equal < [PREDCONST];
MATTACH Equal dar [PREDCONST] OBJ::PREDCONST:=;
MATTACH < dar [PREDCONST] OBJ::PREDCONST:<;
ATTACH pred1apply TO [PREDCONST,TERM=WFF] predappl1\-mak;
ATTACH pred2apply TO [PREDCONST,TERM,TERM=WFF] predappl2\-mak;

DECLARE FUNCONST fun1apply (FUNCONST TERM)=TERM;
DECLARE FUNCONST fun2apply (FUNCONST TERM TERM)=TERM;
DECLARE INDCONST zro [INDCONST];
DECLARE INDCONST suc + - [FUNCONST];
MATTACH zro dar [INDCONST] OBJ::INDCONST:zro;
MATTACH suc dar [FUNCONST] OBJ::FUNCONST:suc;
MATTACH + dar [FUNCONST] OBJ::FUNCONST:+;
MATTACH - dar [FUNCONST] OBJ::FUNCONST:-;
ATTACH fun1apply TO [FUNCONST,TERM=TERM] funappl1\-mak;
ATTACH fun2apply TO [FUNCONST,TERM,TERM=TERM] funappl2\-mak;

DECLARE indvar x y z [TERM];
DECLARE indvar w r [WFF];
DECLARE indvar vl [FACT];
DECLARE indvar op [FUNCONST];

DECLARE PREDCONST NUMERAL 1;
DECLARE PREDCONST numeral 3;
DEFLAM numeral (X zro suc) (OR (EQ X zro) (AND (EQ (CAR X) suc) (numeral (CADR X) zro suc)));
ATTACH numeral TO [TERM,INDCONST,FUNCONST] numeral;
AXIOM AX_NUMERAL: forall x.(NUMERAL(x) iff numeral(x,zro,suc));

DECLARE PREDCONST EQU 1;
DECLARE PREDCONST SOLVE_THM LINEAREQ SUMEQ DIFFEQ 2;
AXIOM AX_LINEAREQ: forall w x.(LINEAREQ(w,x) iff ((EQU(w) and (SUMEQ(w,x) or DIFFEQ(w,x))) and (NUMERAL(rarg(lhs(w))) and NUMERAL(rhs(w)))));
AXIOM AX_EQU: forall w.(EQU(w) iff pred2apply(Equal,lhs(w),rhs(w))=w);
AXIOM AX_SUMEQ: forall w x.(SUMEQ(w,x) iff fun2apply(+,larg(lhs(w)),rarg(lhs(w)))=lhs(w));
AXIOM AX_DIFFEQ: forall w x.(DIFFEQ(w,x) iff fun2apply(-,larg(lhs(w)),rarg(lhs(w)))=lhs(w));
DECLARE FUNCONST solve (WFF TERM)=TERM;
AXIOM AX_SOLVE: forall w x.(solve(w, x)=
  trmif SUMEQ(w, x)
  then fun2apply(-,rhs(w),rarg(lhs(w)))
  else fun2apply(+,rhs(w),rarg(lhs(w))));
DECLARE FUNCONST ifSolvable (WFF TERM WFF)=WFF;
AXIOM AX_SOLVABLE: forall w x r.(ifSolvable(w, x, r)=
  trmif SUMEQ(w, x)
  then mkimp(pred2apply(<,rarg(lhs(w)),rhs(w)), r)
  else r);

AXIOM AX_SOLVE_THM: forall w x.(SOLVE_THM(w,x) iff (LINEAREQ(w,x) imp THEOREM(ifSolvable(w,x,pred2apply(Equal,x,solve(w,x))))));

AXIOM SOLVE: forall w x.SOLVE_THM(w,x);

AXIOM SOLVE_MINUS_LINEAREQ: forall x y z.SOLVE_THM(pred2apply(Equal,fun2apply(-,x,y),z),x);

SETBASICSIMP meta\-axioms at facts {AX_LINEAREQ,AX_EQU,AX_SUMEQ,AX_DIFFEQ,AX_SOLVE,AX_SOLVABLE,AX_SOLVE_THM,AX_NUMERAL};
SETCOMPSIMP EVALSS AT LOGICTREE uni meta\-axioms;

SWITCHCONTEXT OBJ;

nameproof PROOFobj;

makeproof PROOFy;
switchproof PROOFy;
reflect SOLVE (y-suc(suc(zro))=zro) y;
rewrite 1 by LOGICTREE uni PEANO;
decide y = suc(suc(zro)) by 1 2 using ptaut;
theorem THMy 3;

makeproof PROOFx2;
switchproof PROOFx2;
reflect SOLVE (x+suc(suc(zro))=suc(suc(suc(suc(suc(zro)))))) x;
rewrite 1 by LOGICTREE uni PEANO uni TMINUS;
iffe 2 1;
impe 1 3;
eval 4;
iffe 5 1;
impe 4 6;
theorem THx2 7;

makeproof PROOFz;
switchproof PROOFz;
reflect SOLVE_MINUS_LINEAREQ z suc(suc(zro)) suc(suc(suc(zro)));
rewrite 1 by LOGICTREE uni PEANO;
decide z = suc(suc(suc(suc(suc(zro))))) by 1 2 using ptaut;
theorem THMz 3;

switchproof PROOFobj;

show axiom;