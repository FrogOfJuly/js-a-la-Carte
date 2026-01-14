# Modular take on Javascript formalization in Rocq

Inspiration is taken from [Coq a la Carte]([https://github.com/uds-psl/coq-a-la-carte-cpp20/tree/master](https://dl.acm.org/doi/pdf/10.1145/3372885.3373817?casa_token=6rfiSgn-oHoAAAAA:UyHouiN8WO2iArwO5ivJzmd44GC4Ml9a8AnFJAXVFoEBtgmdSDHxmiQk-PqVvRcoLL_2R8a5q5w61Q) paper and its [implementation](https://github.com/uds-psl/coq-a-la-carte-cpp20/tree/master).

## Build

[Install opam](https://opam.ocaml.org/doc/Install.html)

```bash
opam switch create modular_js --packages="ocaml-variants.4.14.0+options,ocaml-option-flambda"
eval $(opam env)
opam pin add coq 9.0.0
opam pin add rocq-equations 1.3.1+9.0
coq_makefile -f _CoqProject -o Makefile && make
```

