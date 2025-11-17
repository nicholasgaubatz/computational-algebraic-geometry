                                                                                                                                            2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y  - y y  - y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y )}
                              4 5    4 9    5 9   3 5    3 7    5 7   6 7 8    6 7 9    6 8 9    7 8 9   3 4 6    3 4 8    3 6 8    4 6 8   1   2   3   4   5   6   7   8   9
                                2   2   2   2   2               2   2   2   2
          AOTinIdeal => ideal (y , y , y , y , y , y y , y y , y , y , y , y , y y y , y y y , y y y )
                                9   8   7   6   5   4 5   3 5   4   3   2   1   6 7 8   3 4 7   3 4 6
          graph => {set {0, 3}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}
                                 2      3      4      5      6
          hSeries => 1 + 9T + 34T  + 68T  + 75T  + 43T  + 10T
          hyperplanes => {a - d, a - g, b - e, c - e, e - g, b - f, b - g, c - f, c - g}
          numVariables => 9
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_9]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_4*y_5-y_4*y_9-y_5*y_9, y_3*y_5-y_3*y_7-y_5*y_7, y_6*y_7*y_8-y_6*y_7*y_9-y_6*y_8*y_9+y_7*y_8*y_9, y_3*y_4*y_6-y_3*y_4*y_8-y_3*y_6*y_8+y_4*y_6*y_8, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}},{{y_9^2, y_8^2, y_7^2, y_6^2, y_5^2, y_4*y_5, y_3*y_5, y_4^2, y_3^2, y_2^2, y_1^2, y_6*y_7*y_8, y_3*y_4*y_7, y_3*y_4*y_6}})
G = graph {set {0, 3}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}
