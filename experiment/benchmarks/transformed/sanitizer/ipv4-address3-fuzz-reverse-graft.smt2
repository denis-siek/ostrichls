(declare-const IPAddr String)
(declare-const o1 String)
(declare-const o2 String)
(declare-const o3 String)
(declare-const o4 String)
(assert (str.in.re IPAddr (re.union (re.union (re.+ (re.range "0" "2")) (re.union (re.* (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (re.++ (re.union (str.to.re "D") (re.union (re.union (re.+ (re.range "0" "2")) (re.++ (re.* (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (re.union (re.* (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.* (re.range "0" "9")))) (str.to.re "")))) (re.union (re.+ (str.to.re "")) (re.++ (re.* (re.range "0" "9")) (re.* (re.range "0" "9"))))) (re.range "0" "2")))))
(assert (= IPAddr (str.++ (str.++ (str.++ (str.++ (str.++ "." o3) (str.++ o4 "")) o2) "") o1)))
(assert (and (>= (str.to.int o1) 0) (>= (str.to.int o2) 0) (>= (str.to.int o3) 2) (>= (str.to.int o4) 2)))
(assert (or (= (str.len o1) 0) (= (str.len o2) 0) (= (str.to.int o3) 2) (= 5 0)))
(assert (and (<= (str.to.int o1) 4) (<= (str.to.int o2) (str.to.int o4)) (<= (str.to.int o3) 1) (<= (str.to.int o4) 3)))
(check-sat)
