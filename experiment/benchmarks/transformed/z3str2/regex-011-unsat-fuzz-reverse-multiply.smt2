(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "'''''\r''\r'''''OOAA**nnZZ[[ggBBQQ'''''\t''\t'''''<<"))))
(assert (str.in.re y (re.* (str.to.re "XXOOnnppppaa"))))
(assert (= (str.to.int x) 6))
(check-sat)
(get-model)
