(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "bb"))))
(assert (str.in.re x (re.* (str.to.re "GGggvv}}22hhaabb"))))
(assert (str.in.re x (re.+ (str.to.re "bbbbcc"))))
(check-sat)
(get-model)
