(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (= (str.++ x y) (str.++ m n)))
(assert (str.in.re n (re.+ (str.to.re "^axnKM''\x0c''e9D=g''\t'''""AgC?24j''\r''''\t''#:-''\r''H"))))
(assert (> (str.to.int x) (str.to.int m)))
(check-sat)
(get-model)
