(declare-const IPAddr String)
(assert (str.in.re IPAddr (re.++ (re.union (re.+ (re.range "0" "2")) (re.++ (re.* (re.range "0" "9")) (re.* (re.range "0" "9")))) (re.union (str.to.re "wed") (re.union (re.union (re.* (re.range "0" "2")) (re.union (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (str.to.re "d&") (re.++ (re.++ (re.* (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.union (str.to.re "30?") (re.union (re.* (re.range "0" "2")) (re.union (re.* (re.range "0" "9")) (re.* (re.range "0" "9"))))))))))))
(assert (not (str.in.re IPAddr (re.++ (re.++ (re.union (str.to.re "9oWmb5X()M") (re.range "0" "5")) (re.++ (re.++ (str.to.re "QM") (re.union (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.++ (str.to.re "fpD") (str.to.re "11"))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.union (str.to.re "ma") (re.union (re.++ (re.++ (str.to.re "2;z'\r''\t'h#") (re.range "0" "5")) (re.union (re.++ (str.to.re "2~") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.union (str.to.re "q'\t'?D") (str.to.re ".qF"))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "[kQc") (re.union (re.++ (re.++ (str.to.re "2kzT^5") (re.range "0" "5")) (re.++ (re.++ (str.to.re "22") (re.union (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "+y") (str.to.re ")@_"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "dU") (re.++ (re.union (str.to.re "2tG'\t'$,P") (re.range "0" "5")) (re.union (re.union (str.to.re "{") (re.union (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.++ (str.to.re "00") (str.to.re "11"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))))))))))))
(check-sat)
