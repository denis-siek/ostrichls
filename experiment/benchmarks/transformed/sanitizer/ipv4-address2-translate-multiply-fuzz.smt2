(declare-const IPAddr String)
(assert (>= (str.to.int IPAddr) 14))
(assert (<= (str.to.int IPAddr) 22))
(assert (str.in.re IPAddr (re.++ (re.++ (re.+ (re.range "0" "2")) (re.++ (re.* (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (str.to.re "CH") (re.++ (re.++ (re.+ (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.* (re.range "0" "9")))) (re.union (str.to.re "'\x0b'") (re.union (re.++ (re.* (re.range "0" "2")) (re.union (re.+ (re.range "0" "9")) (re.* (re.range "0" "9")))) (re.union (str.to.re "H") (re.++ (re.* (re.range "0" "2")) (re.union (re.+ (re.range "0" "9")) (re.* (re.range "0" "9"))))))))))))
(assert (not (str.in.re IPAddr (re.union (re.union (re.++ (str.to.re "2|Ik!i") (re.range "0" "5")) (re.union (re.++ (str.to.re "2") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "") (str.to.re "-w"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.union (str.to.re "'\x0b''\x0b'H") (re.++ (re.union (re.union (str.to.re ":v1ed]5M") (re.range "0" "5")) (re.union (re.++ (str.to.re "Q") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.++ (str.to.re "00") (str.to.re "1G'\t'"))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.union (str.to.re "Hc`") (re.++ (re.++ (re.++ (str.to.re "2tnB") (re.range "0" "5")) (re.union (re.union (str.to.re "22") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.++ (str.to.re "'\x0b'") (str.to.re "]6w"))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "HH") (re.++ (re.++ (str.to.re "2w5") (re.range "0" "5")) (re.union (re.union (str.to.re "") (re.union (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.++ (str.to.re "0") (str.to.re "11"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))))))))))))
(check-sat)
