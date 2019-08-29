declare sort NATNUM;
declare indvar n m p q [NATNUM];
declare indconst zro [NATNUM];
declare funconst suc prd (NATNUM) = NATNUM;
declare funconst +(NATNUM,NATNUM) = NATNUM [inf = 450 455];
declare funconst *(NATNUM,NATNUM) = NATNUM [inf = 550 555];
declare predconst < 2 [inf];
declare predpar P 1;

axiom ONEONE: forall n m.(suc(n)=suc(m) imp n=m);
axiom SUCC1: forall n.not(zro=suc(n));
axiom SUCC2: forall n.not(zro=n) imp exists m.n=suc(m);
axiom PLUS0: forall n. n + zro = n;
axiom PLUS: forall n m. n+suc(m)=suc(n+m);
axiom TIMES0: forall n. n * zro = n;
axiom TIME: forall n m. n*suc(m)=(n*m)+m;

axiom INDUCT: P(zro) and forall n.(P(n) imp P(suc(n))) imp forall n.P(n);

decrep NATNUMREP;
represent {NATNUM} as NATNUMREP;
attach zro to 0;
attach suc to ADD1;
deflam prd(x) (COND ((> x 0) (SUB1 x)) (T 0));
attach prd to prd;
attach + to +;
attach * to *;
attach < to <;
