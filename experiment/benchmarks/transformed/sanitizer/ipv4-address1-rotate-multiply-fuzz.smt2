(declare-const IPAddr String)
(assert (str.in.re IPAddr (re.union (re.union (re.* (re.+ (re.range "0" "9"))) (re.range "0" "9")) (re.* (re.union (re.range "0" "2") (re.++ (re.++ (re.+ (re.* (re.range "0" "9"))) (re.range "0" "9")) (re.union (re.+ (re.union (re.range "0" "2") (re.++ (re.union (re.+ (re.+ (re.range "0" "9"))) (re.range "0" "9")) (re.union (re.+ (re.union (re.range "0" "2") (re.union (re.+ (re.union (re.+ (re.+ (re.range "0" "9"))) (re.range "0" "9"))) (re.++ (re.range "0" "2") (str.to.re "._"))))) (str.to.re "s4"))))) (str.to.re ")'\x0b'."))))))))
(assert (not (str.in.re IPAddr (re.++ (re.range "0" "5") (re.union (re.union (re.++ (re.++ (re.range "0" "9") (str.to.re "")) (re.union (re.range "0" "9") (re.union (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "") (str.to.re "1")))))) (re.range "0" "4")) (re.++ (str.to.re "255") (re.++ (re.range "0" "5") (re.++ (re.union (re.++ (re.++ (re.union (re.range "0" "9") (str.to.re "22")) (re.++ (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "0") (str.to.re "1")))))) (re.range "0" "4")) (re.++ (str.to.re "2j") (re.++ (re.range "0" "5") (re.union (re.union (re.union (re.union (re.union (re.range "0" "9") (str.to.re "'\n'' '")) (re.++ (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "0") (str.to.re "")))))) (re.range "0" "4")) (re.union (str.to.re "W5bGM") (re.union (re.union (re.range "0" "5") (re.union (re.++ (re.union (re.range "0" "9") (str.to.re ">")) (re.++ (re.range "0" "9") (re.union (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "C'\n'") (str.to.re "D")))))) (re.range "0" "4"))) (re.++ (str.to.re "25") (str.to.re "."))))) (str.to.re "H/"))))) (str.to.re "'W}w")))))))))
(check-sat)
