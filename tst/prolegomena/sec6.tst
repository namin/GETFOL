fetch ../tst/prolegomena/appa.tst;

declare funconst fact(NATNUM)=NATNUM;
axiom FACT: forall n.fact(n)=trmif n=0 then 1 else n*fact(prd(n))