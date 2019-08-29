fetch ../tst/prolegomena/appa.tst;
fetch ../tst/prolegomena/appb.tst;

simplify Null(nil);

setbasicsimp S1 at facts {1};

rewrite rev(cons(x,nil)) by Basic uni Funs uni S1 uni LOGICTREE;
