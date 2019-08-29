fetch ../tst/prolegomena/appa.tst;

declare funconst fact(NATNUM)=NATNUM;
axiom FACT: forall n.fact(n)=trmif n=zro then suc(zro) else n*fact(prd(n));