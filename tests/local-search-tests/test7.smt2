(set-logic QF_S)

(declare-fun H () String)
(declare-fun G () String)
(declare-fun E () String)
(declare-fun J () String)
(assert (= (str.++  "de" H "fahgf" E H "bg" H J H "dg")
           (str.++  "deifah" G "idg") ))
(check-sat)
(get-model)


