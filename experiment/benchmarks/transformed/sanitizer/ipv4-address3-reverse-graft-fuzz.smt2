(declare-const IPAddr String)
(declare-const o1 String)
(declare-const o2 String)
(declare-const o3 String)
(declare-const o4 String)
(assert (str.in.re IPAddr (re.union (re.union (re.++ (re.++ (re.union (re.++ (re.union (re.++ (re.+ (re.range "0" "9")) (re.* (re.range "0" "9"))) (re.* (re.range "0" "2"))) (str.to.re "v")) (re.union (re.union (re.+ (re.range "0" "9")) (re.* (re.range "0" "9"))) (re.+ (re.range "0" "2")))) (str.to.re "")) (re.++ (re.union (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9"))) (re.* (re.range "0" "2")))) (re.range "0" "2")) (re.union (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9"))) (re.* (str.to.re "I"))))))
(assert (= IPAddr (str.++ (str.++ (str.++ (str.++ "." (str.++ (str.++ o4 ".") o3)) o2) "") o1)))
(assert (and (>= (str.to.int o1) 1) (>= (str.len o2) 1) (>= (str.len o3) 2) (>= (str.len o4) 2)))
(assert (or (= (str.len o1) 2) (= (str.to.int o2) 1) (= (str.to.int o3) 2) (= (str.len o4) 1)))
(assert (and (<= (str.len o1) 3) (<= (str.len o2) 2) (<= 4 3) (<= (str.to.int o4) (str.to.int o3))))
(check-sat)
