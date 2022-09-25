(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.union (str.to.re "dd""""AAcc11aatt") (str.to.re "dd{{")))))
(assert (= 42 (str.to.int x)))
(assert (not (= x "33pphhFFtt$$==]];;]]++$$[[tt1122""""\\\\")))
(assert (not (= x "\\\\44QQ[[||##JJ33**ttff]]ww]]''BBdd7711^^DD--88'''\r''\r'''WW\\\\uugg66'''\x0c''\x0c'''2200vvhh||KK]]<<]]BB>>tt'''\t''\t'''")))
(check-sat)
(get-model)
