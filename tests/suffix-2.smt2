(set-logic QF_S)

(declare-const x String)

(assert (not (= (str.suffixof x "A") true)))

(check-sat)
