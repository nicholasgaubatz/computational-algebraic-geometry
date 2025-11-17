                                                                                                                                            2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y  - y y  - y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y )}
                              3 4    3 8    4 8   2 4    2 6    4 6   5 6 7    5 6 8    5 7 8    6 7 8   2 3 5    2 3 7    2 5 7    3 5 7   1   2   3   4   5   6   7   8
                                2   2   2   2   2               2   2   2
          AOTinIdeal => ideal (y , y , y , y , y , y y , y y , y , y , y , y y y , y y y , y y y )
                                8   7   6   5   4   3 4   2 4   3   2   1   5 6 7   2 3 6   2 3 5
          graph => {set {0, 3}, set {1, 4}, set {2, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}
                                 2      3      4      5
          hSeries => 1 + 8T + 26T  + 42T  + 33T  + 10T
          hyperplanes => {a - d, b - e, c - e, e - g, b - f, b - g, c - f, c - g}
          numVariables => 8
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_8]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_3*y_4-y_3*y_8-y_4*y_8, y_2*y_4-y_2*y_6-y_4*y_6, y_5*y_6*y_7-y_5*y_6*y_8-y_5*y_7*y_8+y_6*y_7*y_8, y_2*y_3*y_5-y_2*y_3*y_7-y_2*y_5*y_7+y_3*y_5*y_7, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}},{{y_8^2, y_7^2, y_6^2, y_5^2, y_4^2, y_3*y_4, y_2*y_4, y_3^2, y_2^2, y_1^2, y_5*y_6*y_7, y_2*y_3*y_6, y_2*y_3*y_5}})
G = graph {set {0, 3}, set {1, 4}, set {2, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}
