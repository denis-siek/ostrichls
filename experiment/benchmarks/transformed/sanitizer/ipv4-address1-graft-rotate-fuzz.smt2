(declare-const IPAddr String)
(assert (str.in.re IPAddr (re.++ (re.union (re.+ (re.* (re.range "0" "9"))) (re.range "0" "9")) (re.* (re.union (re.range "0" "2") (re.++ (re.++ (re.+ (re.* (re.range "0" "9"))) (re.range "0" "9")) (re.union (re.* (re.++ (re.range "0" "2") (re.++ (re.union (re.+ (re.+ (re.range "0" "9"))) (re.range "0" "9")) (re.union (re.+ (re.++ (re.range "0" "2") (re.union (re.+ (re.++ (re.* (re.* (re.range "0" "9"))) (re.range "0" "9"))) (re.++ (re.range "0" "2") (str.to.re ""))))) (str.to.re "."))))) (str.to.re "P"))))))))
(assert (not (str.in.re IPAddr (re.union (re.range "0" "5") (re.union (re.union (re.union (re.union (re.range "0" "9") (str.to.re "2")) (re.++ (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "") (str.to.re "")))))) (re.range "0" "4")) (re.++ (str.to.re "2#") (re.union (re.range "0" "5") (re.union (re.++ (re.union (re.++ (re.union (re.range "0" "9") (str.to.re "2")) (re.union (re.range "0" "9") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "&") (str.to.re "h")))))) (re.range "0" "4")) (re.++ (str.to.re "45") (re.union (re.range "0" "5") (re.union (re.union (re.union (re.++ (re.union (re.range "0" "9") (str.to.re "")) (re.union (re.range "0" "9") (re.union (re.opt (re.range "0" "9")) (re.opt (re.++ (str.to.re "") (str.to.re "p")))))) (re.range "0" "4")) (re.union (str.to.re "P5") (re.++ (re.union (re.range "0" "5") (re.union (re.++ (re.++ (re.range "0" "9") (str.to.re "2")) (re.union (str.to.re "8") (re.++ (re.opt (re.range "0" "9")) (re.opt (re.union (str.to.re "0") (re.range "0" "9")))))) (re.range "0" "4"))) (re.++ (str.to.re "9ukx") (str.to.re ""))))) (str.to.re "."))))) (str.to.re "")))))))))
(check-sat)
