(declare-const x String)
(declare-const y String)
(assert (= x "aaaaaa4?YNH\\t;(' 'N&_<--JsCq;}1k^po%xz~%{$VDmJ&yl7D0sZf)0t"))
(assert (str.in.re x (re.* (re.+ (str.to.re "c4KA\\\\Lk;f?")))))
(check-sat)
(get-model)
