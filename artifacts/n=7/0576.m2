                                                                                                                            2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y  - y y  - y y , y y y y  - y y y y  - y y y y  + y y y y  - y y y y , y , y , y , y , y , y , y , y , y )}
                              6 7    6 9    7 9   1 2    1 3    2 3   3 4 5 7    3 4 5 8    3 4 7 8    3 5 7 8    4 5 7 8   1   2   3   4   5   6   7   8   9
                                2   2   2         2   2   2   2   2         2
          AOTinIdeal => ideal (y , y , y , y y , y , y , y , y , y , y y , y , y y y y , y y y y y )
                                9   8   7   6 7   6   5   4   3   2   1 2   1   3 4 5 7   3 4 5 6 8
          graph => {set {0, 3}, set {3, 5}, set {0, 5}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 6}, set {1, 5}, set {2, 6}}
                                 2      3      4      5      6
          hSeries => 1 + 9T + 34T  + 70T  + 84T  + 56T  + 16T
          hyperplanes => {a - d, d - f, a - f, a - g, b - e, c - e, e - g, b - f, c - g}
          numVariables => 9
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_9]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-4}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_6*y_7-y_6*y_9-y_7*y_9, y_1*y_2-y_1*y_3-y_2*y_3, y_3*y_4*y_5*y_7-y_3*y_4*y_5*y_8-y_3*y_4*y_7*y_8+y_3*y_5*y_7*y_8-y_4*y_5*y_7*y_8, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-4}, {-5}},{{y_9^2, y_8^2, y_7^2, y_6*y_7, y_6^2, y_5^2, y_4^2, y_3^2, y_2^2, y_1*y_2, y_1^2, y_3*y_4*y_5*y_7, y_3*y_4*y_5*y_6*y_8}})
G = graph {set {0, 3}, set {3, 5}, set {0, 5}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 6}, set {1, 5}, set {2, 6}}
