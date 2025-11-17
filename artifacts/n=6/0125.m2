                                                                                                              2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  + y y , y y  - y y  - y y , y y  - y y  + y y , y y  - y y  - y y , y , y , y , y , y , y , y , y , y )}
                              7 8    7 9    8 9   5 6    5 8    6 8   3 4    3 9    4 9   1 2    1 3    2 3   1   2   3   4   5   6   7   8   9
                                2   2         2   2         2   2         2   2         2
          AOTinIdeal => ideal (y , y , y y , y , y , y y , y , y , y y , y , y , y y , y )
                                9   8   7 8   7   6   5 6   5   4   3 4   3   2   1 2   1
          graph => {set {0, 2}, set {2, 4}, set {0, 4}, set {0, 5}, set {1, 3}, set {3, 5}, set {1, 4}, set {1, 5}, set {4, 5}}
                                 2      3      4      5
          hSeries => 1 + 9T + 32T  + 56T  + 48T  + 16T
          hyperplanes => {a - c, c - e, a - e, a - f, b - d, d - f, b - e, b - f, e - f}
          numVariables => 9
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_9]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_7*y_8-y_7*y_9+y_8*y_9, y_5*y_6-y_5*y_8-y_6*y_8, y_3*y_4-y_3*y_9+y_4*y_9, y_1*y_2-y_1*y_3-y_2*y_3, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_9^2, y_8^2, y_7*y_8, y_7^2, y_6^2, y_5*y_6, y_5^2, y_4^2, y_3*y_4, y_3^2, y_2^2, y_1*y_2, y_1^2}})
G = graph {set {0, 2}, set {2, 4}, set {0, 4}, set {0, 5}, set {1, 3}, set {3, 5}, set {1, 4}, set {1, 5}, set {4, 5}}
