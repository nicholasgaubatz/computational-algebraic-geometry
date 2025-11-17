                                                                                                              2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y  - y y  + y y , y y  - y y  - y y , y y  - y y  - y y , y , y , y , y , y , y , y , y , y )}
                              7 8    7 9    8 9   4 5    4 8    5 8   2 3    2 6    3 6   1 3    1 5    3 5   1   2   3   4   5   6   7   8   9
                                2   2         2   2   2         2   2               2   2
          AOTinIdeal => ideal (y , y , y y , y , y , y , y y , y , y , y y , y y , y , y , y y y , y y y y )
                                9   8   7 8   7   6   5   4 5   4   3   2 3   1 3   2   1   1 2 5   1 2 4 6
          graph => {set {0, 3}, set {1, 3}, set {3, 5}, set {0, 4}, set {0, 5}, set {1, 5}, set {2, 4}, set {4, 5}, set {2, 5}}
                                 2      3      4      5
          hSeries => 1 + 9T + 32T  + 56T  + 48T  + 16T
          hyperplanes => {a - d, b - d, d - f, a - e, a - f, b - f, c - e, e - f, c - f}
          numVariables => 9
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_9]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_7*y_8-y_7*y_9-y_8*y_9, y_4*y_5-y_4*y_8+y_5*y_8, y_2*y_3-y_2*y_6-y_3*y_6, y_1*y_3-y_1*y_5-y_3*y_5, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-4}},{{y_9^2, y_8^2, y_7*y_8, y_7^2, y_6^2, y_5^2, y_4*y_5, y_4^2, y_3^2, y_2*y_3, y_1*y_3, y_2^2, y_1^2, y_1*y_2*y_5, y_1*y_2*y_4*y_6}})
G = graph {set {0, 3}, set {1, 3}, set {3, 5}, set {0, 4}, set {0, 5}, set {1, 5}, set {2, 4}, set {4, 5}, set {2, 5}}
