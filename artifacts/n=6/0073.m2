                                                                                          2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y  - y y  + y y , y y  - y y  - y y , y , y , y , y , y , y , y , y )}
                              5 7    5 8    7 8   3 4    3 7    4 7   1 2    1 4    2 4   1   2   3   4   5   6   7   8
                                2   2         2   2   2         2   2         2
          AOTinIdeal => ideal (y , y , y y , y , y , y , y y , y , y , y y , y )
                                8   7   5 7   6   5   4   3 4   3   2   1 2   1
          graph => {set {0, 3}, set {3, 5}, set {0, 4}, set {0, 5}, set {1, 4}, set {2, 4}, set {4, 5}, set {1, 5}}
                                 2      3      4     5
          hSeries => 1 + 8T + 25T  + 38T  + 28T  + 8T
          hyperplanes => {a - d, d - f, a - e, a - f, b - e, c - e, e - f, b - f}
          numVariables => 8
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_8]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_5*y_7-y_5*y_8-y_7*y_8, y_3*y_4-y_3*y_7+y_4*y_7, y_1*y_2-y_1*y_4-y_2*y_4, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_8^2, y_7^2, y_5*y_7, y_6^2, y_5^2, y_4^2, y_3*y_4, y_3^2, y_2^2, y_1*y_2, y_1^2}})
G = graph {set {0, 3}, set {3, 5}, set {0, 4}, set {0, 5}, set {1, 4}, set {2, 4}, set {4, 5}, set {1, 5}}
