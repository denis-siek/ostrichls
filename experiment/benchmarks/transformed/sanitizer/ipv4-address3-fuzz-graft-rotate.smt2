(declare-const IPAddr String)
(declare-const o1 String)
(declare-const o2 String)
(declare-const o3 String)
(declare-const o4 String)
(assert (str.in.re IPAddr (re.union (re.union (re.* (re.+ (re.range "0" "9"))) (re.range "0" "9")) (re.+ (re.union (re.range "0" "2") (re.++ (re.++ (re.* (re.* (re.range "0" "9"))) (re.range "0" "9")) (re.++ (re.+ (re.union (re.range "0" "2") (re.union (re.++ (re.+ (re.* (re.range "0" "9"))) (re.range "0" "9")) (re.union (re.+ (re.union (re.range "0" "2") (re.++ (re.* (re.++ (re.* (re.+ (str.to.re ""))) (re.range "0" "9"))) (re.union (re.range "0" "2") (str.to.re ""))))) (str.to.re "D"))))) (re.range "0" "9"))))))))
(assert (= IPAddr (str.++ (str.++ o4 (str.++ o3 ".")) (str.++ (str.++ (str.++ "" o2) "") o1))))
(assert (and (>= (str.to.int o1) 0) (>= (str.to.int o2) 0) (>= (str.to.int o3) 2) (>= (str.to.int o4) 2)))
(assert (or (= (str.len o1) 0) (= (str.len o2) 0) (= (str.to.int o3) 2) (= (str.to.int o4) 0)))
(assert (and (<= (str.to.int o1) 4) (<= (str.to.int o2) 5) (<= (str.to.int o3) 1) (<= 3 (str.to.int o4))))
(check-sat)
