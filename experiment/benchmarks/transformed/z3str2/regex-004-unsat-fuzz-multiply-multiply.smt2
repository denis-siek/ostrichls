(declare-const x String)
(assert (= x "bbbbcccccccc####%%%%pppp"))
(assert (str.in.re x (re.++ (re.+ (str.to.re ")))),,,,bbbbccccdddd")) (re.+ (str.to.re "cccc>>>>7777????")))))
(check-sat)
(get-model)
