(declare-const x String)
(declare-const y String)
(assert (str.in.re y (re.+ (re.+ (str.to.re "B<G%^P-yJfN' 'Ojz&mh*'\r''\x0c'^$'\r'wx'%(7EKt_'\r'9Z4/jihCEnbb+W%j' 'NJ'\x0b'`T'\x0b'y6WVy8^/X#y~C)(Rxmp*UG7I9bC<H'\x0b'08\\]qfHg9T2wDB{Sl1#tZHU'\x0c'g*WIsLK-<1i6'`x#9T%8hYP(@=v$''\t''Rg`'\x0c'7[emM_hx;/Pi;f.mk4$|D,Mt9;?;L8M'\x0b'7L<&n'\t'kiqP]W""%E5'\t'/E")))))
(assert (= (str.to.int y) 2))
(check-sat)
(get-model)
