# Prolegomena

Examples inspired from Weyhrauch's _Prolegomena_ ([PDF](https://apps.dtic.mil/dtic/tr/fulltext/u2/a065698.pdf), [alt. PDF](https://pdfs.semanticscholar.org/07b8/2b58e1fd76540cf2217ed4537136855685d5.pdf)).

# ToC

## Paper
- [sec2.tst](sec2.tst): syllogism.
- [sec6.tst](sec6.tst): factorial.
- [sec9.tst](sec9.tst): reflection principle. _"Change theorem proving in the theory into evaluation in the metatheory."_
- [sec91.tst](sec91.tst): linear equations by hand and by reflecting the algebra.
- [appa.tst](appa.tst): an axiomatization of natural numbers.
- [appb.tst](appb.tst): an axiomatization of s-expressions.
- [appd.tst](appd.tst): semantic evaluations.
- [appe.tst](appe.tst): syntactic simplification.

## Hacking
- [underlying.tst](underlying.tst): alternative evaluator that prints underlying representation when evaluation is successful, and still applies rewrites when evaluation is successful. Not needed for examples, but convenient.
- [untyped.fol](untyped.fol): by-passes the finnicky check for type representation. Then [appd_untyped.tst](appd_untyped.tst) works.

## See also
- [axiom](../../axiom)
