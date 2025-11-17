                                                                                                                                                                               2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y  - y y  - y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y y y  + y y y  - y y y  - y y y , y , y , y , y , y , y , y , y , y )}
                              6 7    6 9    7 9   1 2    1 5    2 5   2 3 8    2 3 9    2 8 9    3 8 9   4 5 6    4 5 8    4 6 8    5 6 8   1 3 4    1 3 7    1 4 7    3 4 7   1   2   3   4   5   6   7   8   9
                                2   2   2         2   2   2   2   2         2
          AOTinIdeal => ideal (y , y , y , y y , y , y , y , y , y , y y , y , y y y , y y y , y y y , y y y y , y y y y , y y y y )
                                9   8   7   6 7   6   5   4   3   2   1 2   1   2 3 8   4 5 6   1 3 4   4 5 7 8   1 3 5 8   2 3 4 5
          graph => {set {0, 2}, set {2, 4}, set {2, 5}, set {0, 3}, set {0, 4}, set {1, 3}, set {3, 5}, set {1, 4}, set {1, 5}}
                                 2      3      4      5
          hSeries => 1 + 9T + 34T  + 67T  + 67T  + 26T
          hyperplanes => {a - c, c - e, c - f, a - d, a - e, b - d, d - f, b - e, b - f}
          numVariables => 9
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_9]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_6*y_7-y_6*y_9-y_7*y_9, y_1*y_2-y_1*y_5-y_2*y_5, y_2*y_3*y_8-y_2*y_3*y_9-y_2*y_8*y_9+y_3*y_8*y_9, y_4*y_5*y_6-y_4*y_5*y_8-y_4*y_6*y_8+y_5*y_6*y_8, y_1*y_3*y_4+y_1*y_3*y_7-y_1*y_4*y_7-y_3*y_4*y_7, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-4}, {-4}, {-4}},{{y_9^2, y_8^2, y_7^2, y_6*y_7, y_6^2, y_5^2, y_4^2, y_3^2, y_2^2, y_1*y_2, y_1^2, y_2*y_3*y_8, y_4*y_5*y_6, y_1*y_3*y_4, y_4*y_5*y_7*y_8, y_1*y_3*y_5*y_8, y_2*y_3*y_4*y_5}})
G = graph {set {0, 2}, set {2, 4}, set {2, 5}, set {0, 3}, set {0, 4}, set {1, 3}, set {3, 5}, set {1, 4}, set {1, 5}}
