(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (= (str.++ x y) (str.++ m n)))
(assert (str.in.re n (str.to.re "=]:~ng+a9j(JAm'\t'O''\n'$2m@i##w7PjzE5.")))
(assert (> (str.to.int x) (str.to.int m)))
(check-sat)
(get-model)
