fetch ../tst/prolegomena/appa.tst;

declare funconst fact(NATNUM)=NATNUM;
axiom FACT: forall n.fact(n)=trmif n=zro then suc(zro) else n*fact(prd(n));

simplify (zro=zro iff TRUE);
setbasicsimp N0 at facts {1};
setbasicsimp FACT_UNFOLD at facts {FACT};
rewrite (fact(zro)) by N0 uni FACT_UNFOLD uni LOGICTREE;
setbasicsimp F0 at facts {2};

simplify (suc(zro)=zro iff FALSE);
setbasicsimp N1 at facts {3};

axiom PRDSUC: forall n. prd(suc(n))=n;
setbasicsimp PRDSUC at facts {PRDSUC};

rewrite (fact(suc(zro))) by N0 uni N1 uni FACT_UNFOLD uni PRDSUC uni LOGICTREE;

simplify (suc(suc(zro))=zro iff FALSE);
setbasicsimp N2 at facts {5};

simplify (suc(suc(suc(zro)))=zro iff FALSE);
setbasicsimp N3 at facts {6};

rewrite (fact(suc(suc(suc(zro))))) by N0 uni N1 uni N2 uni N3 uni FACT_UNFOLD uni PRDSUC uni LOGICTREE;

rewrite (fact(suc(suc(suc(zro))))) by N0 uni N1 uni N2 uni N3 uni FACT_UNFOLD uni PRDSUC uni PEANO uni LOGICTREE;

axiom EQSYM: forall n m.(n = m iff m = n);
setbasicsimp EQSYM at facts {EQSYM};

rewrite forall n.(suc(n)=zro iff FALSE) by PEANO uni EQSYM uni LOGICTREE;
setbasicsimp NS at facts {9};

declare indvar X Y;
axiom IFY: forall X Y.((trmif FALSE then X else Y) = Y);
setbasicsimp IFY at facts {IFY};

rewrite (fact(suc(suc(suc(zro))))) by N0 uni NS uni FACT_UNFOLD uni PRDSUC uni PEANO uni IFY uni LOGICTREE;

rewrite (fact(suc(suc(suc(suc(zro)))))) by N0 uni NS uni FACT_UNFOLD uni PRDSUC uni PEANO uni IFY uni LOGICTREE;