(declare-const x String)
(assert (= x "Xw'\n'@QRge4F\\Q#5rPZj4Phid"))
(assert (str.in.re x (re.* (re.union (str.to.re "uWYnYXf^Z\\") (str.to.re "h?'\x0c'W")))))
(check-sat)
(get-model)
