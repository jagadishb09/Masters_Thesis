(IN-PACKAGE "ACL2")

(include-book "workshops/2003/cowles-gamboa-van-baalen_matrix/support/matalg" :dir :system)

(defthm normalize-header-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (header name l)
                  (header :fake-name l)))
  :hints (("Goal" :in-theory (e/d (header) ()))))

(defthm normalize-default-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (default name l)
                  (default :fake-name l)))
  :hints (("Goal" :in-theory (e/d (default) ()))))

(defthm normalize-maximum-length-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (maximum-length name l)
                  (maximum-length :fake-name l)))
  :hints (("Goal" :in-theory (e/d (maximum-length) ()))))

(defthm normalize-dimensions-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (dimensions name l)
                  (dimensions :fake-name l)))
  :hints (("Goal" :in-theory (e/d (dimensions) ()))))

(defthm normalize-compress11-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress11 name l i n default)
                  (compress11 :fake-name l i n default)))
  :hints (("Goal" :in-theory (e/d (compress11) ()))))

(defthm normalize-compress1-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress1 name l)
                  (compress1 :fake-name l)))
  :hints (("Goal" :in-theory (e/d (compress1) ()))))

(defthm normalize-compress211-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress211 name l i x j default)
                  (compress211 :fake-name l i x j default)))
  :hints (("Goal" :in-theory (e/d (compress211) ()))))

(defthm normalize-compress21-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress21 name l n i j default)
                  (compress21 :fake-name l n i j default)))
  :hints (("Goal" :in-theory (e/d (compress21) ()))))

(defthm normalize-compress2-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (compress2 name l)
                  (compress2 :fake-name l)))
  :hints (("Goal" :in-theory (e/d (compress2) ()))))

(defthm normalize-aref2-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (aref2 name l i j)
                  (aref2 :fake-name l i j)))
  :hints (("Goal" :in-theory (e/d (aref2) ()))))

(defthm normalize-array2p-name
  (implies (and (syntaxp (not (equal name '':fake-name)))
		(symbolp name))
           (equal (array2p name l)
                  (array2p :fake-name l)))
  :hints (("Goal" :in-theory (e/d (array2p) ()))))

(defthm normalize-alist2p-name
  (implies (and (syntaxp (not (equal name '':fake-name)))
		(symbolp name))
           (equal (alist2p name l)
                  (alist2p :fake-name l)))
  :hints (("Goal" :in-theory (e/d (alist2p) ()))))
