(declare-const S String)
(assert (not (str.in.re S (re.++ (str.to.re "_G-G6cD?Lj\\!K!,d&KKK") re.allchar))))
(assert (str.in.re S (re.union (re.++ (re.++ (str.to.re "H9B") re.allchar) (str.to.re "cZGG'\r'G)nsu' 'VUK=zIC")) re.allchar)))
(check-sat)
(get-model)
(get-info :reason-unknown)
