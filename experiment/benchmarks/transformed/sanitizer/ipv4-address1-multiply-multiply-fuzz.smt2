(declare-const IPAddr String)
(assert (str.in.re IPAddr (re.++ (re.++ (re.* (re.range "0" "2")) (re.union (re.+ (re.range "0" "9")) (re.* (re.range "0" "9")))) (re.++ (str.to.re "2'\n'$z?") (re.union (re.union (re.+ (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.* (re.range "0" "9")))) (re.++ (str.to.re "..9_tPQ&$F") (re.union (re.union (re.* (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.* (re.range "0" "9")))) (re.++ (str.to.re "P8ZvUta9") (re.++ (re.+ (re.range "0" "2")) (re.++ (re.* (re.range "0" "9")) (re.* (re.range "0" "9"))))))))))))
(assert (not (str.in.re IPAddr (re.++ (re.union (re.union (str.to.re "xJyr.' 'a#i2;#5") (re.range "0" "5")) (re.++ (re.++ (str.to.re "22CqY#162") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.++ (str.to.re "22") (str.to.re "171"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "..t6+") (re.union (re.++ (re.union (str.to.re "))I+ma2SX]Mm5") (re.range "0" "5")) (re.union (re.++ (str.to.re "We12") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.++ (str.to.re "DrpT!00") (str.to.re ":'\x0b'"))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "ux]0..") (re.union (re.union (re.union (str.to.re "ym*'\x0c'#rVH22555") (re.range "0" "5")) (re.++ (re.++ (str.to.re "2'\t''\x0c'Jlz]cP'\t'(") (re.union (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.++ (str.to.re "000HY") (str.to.re "11@L"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.union (str.to.re "..") (re.++ (re.union (str.to.re "u+(256VL5") (re.range "0" "5")) (re.union (re.++ (str.to.re "2y4(") (re.union (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.++ (str.to.re "0d""q_") (str.to.re "a*1"))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9")))))))))))))))
(check-sat)
