                                                                                                                                                                                                                    2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  + y y , y y y y  - y y y y  + y y y y  - y y y y  - y y y y , y y y y  - y y y y  - y y y y  + y y y y  + y y y y , y y y y  - y y y y  + y y y y  - y y y y  - y y y y , y , y , y , y , y , y , y , y , y )}
                              3 4    3 6    4 6   5 6 7 8    5 6 7 9    5 6 8 9    5 7 8 9    6 7 8 9   1 2 4 8    1 2 4 9    1 2 8 9    1 4 8 9    2 4 8 9   1 2 3 5    1 2 3 7    1 2 5 7    1 3 5 7    2 3 5 7   1   2   3   4   5   6   7   8   9
                                2   2   2   2   2   2         2   2   2
          AOTinIdeal => ideal (y , y , y , y , y , y , y y , y , y , y , y y y y , y y y y , y y y y , y y y y y , y y y y y )
                                9   8   7   6   5   4   3 4   3   2   1   5 6 7 8   1 2 4 8   1 2 3 5   1 2 3 6 8   1 2 4 5 6
          graph => {set {0, 3}, set {3, 5}, set {0, 4}, set {0, 6}, set {1, 4}, set {4, 6}, set {1, 5}, set {2, 5}, set {2, 6}}
                                 2      3       4      5      6
          hSeries => 1 + 9T + 35T  + 77T  + 102T  + 76T  + 24T
          hyperplanes => {a - d, d - f, a - e, a - g, b - e, e - g, b - f, c - f, c - g}
          numVariables => 9
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_9]
AOTideal = ideal map(R^1,R^{{-2}, {-4}, {-4}, {-4}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_3*y_4-y_3*y_6+y_4*y_6, y_5*y_6*y_7*y_8-y_5*y_6*y_7*y_9+y_5*y_6*y_8*y_9-y_5*y_7*y_8*y_9-y_6*y_7*y_8*y_9, y_1*y_2*y_4*y_8-y_1*y_2*y_4*y_9-y_1*y_2*y_8*y_9+y_1*y_4*y_8*y_9+y_2*y_4*y_8*y_9, y_1*y_2*y_3*y_5-y_1*y_2*y_3*y_7+y_1*y_2*y_5*y_7-y_1*y_3*y_5*y_7-y_2*y_3*y_5*y_7, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-4}, {-4}, {-4}, {-5}, {-5}},{{y_9^2, y_8^2, y_7^2, y_6^2, y_5^2, y_4^2, y_3*y_4, y_3^2, y_2^2, y_1^2, y_5*y_6*y_7*y_8, y_1*y_2*y_4*y_8, y_1*y_2*y_3*y_5, y_1*y_2*y_3*y_6*y_8, y_1*y_2*y_4*y_5*y_6}})
G = graph {set {0, 3}, set {3, 5}, set {0, 4}, set {0, 6}, set {1, 4}, set {4, 6}, set {1, 5}, set {2, 5}, set {2, 6}}
