(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (re.++ (str.to.re "aaccHH") (str.to.re "ii00OO")))))
(assert (= 16 (str.len x)))
(assert (not (= x "aa##00BBTTvv44VVhhWW''iiccddBB\\\\//aa@@II@@33%%ffPPnnkkddNNww[[dd")))
(assert (not (= x "aabbbbccddoo::22")))
(check-sat)
(get-model)
