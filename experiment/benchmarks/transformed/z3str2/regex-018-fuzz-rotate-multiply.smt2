(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (re.++ (str.to.re "AABB") (str.to.re "'''''\r''\r'''''VV**22")))))
(assert (= 16 (str.to.int x)))
(assert (not (= x "1199'''''\t''\t'''''zzCCvvSSqqNNBB")))
(check-sat)
(get-model)
