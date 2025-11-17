                                                                                                                                                                              2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y y y y  - y y y y  + y y y y  - y y y y  - y y y y , y , y , y , y , y , y , y , y )}
                              1 3    1 5    3 5   2 3 7    2 3 8    2 7 8    3 7 8   4 5 6    4 5 8    4 6 8    5 6 8   1 2 4 6    1 2 4 7    1 2 6 7    1 4 6 7    2 4 6 7   1   2   3   4   5   6   7   8
                                2   2   2   2   2   2         2   2
          AOTinIdeal => ideal (y , y , y , y , y , y , y y , y , y , y y y , y y y , y y y y , y y y y )
                                8   7   6   5   4   3   1 3   2   1   2 3 7   4 5 6   1 2 5 7   1 2 4 6
          graph => {set {0, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 6}, set {1, 4}, set {1, 5}, set {1, 6}}
                                 2      3      4      5
          hSeries => 1 + 8T + 27T  + 48T  + 44T  + 16T
          hyperplanes => {a - d, d - f, d - g, a - e, a - g, b - e, b - f, b - g}
          numVariables => 8
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_8]
AOTideal = ideal map(R^1,R^{{-2}, {-3}, {-3}, {-4}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_1*y_3-y_1*y_5-y_3*y_5, y_2*y_3*y_7-y_2*y_3*y_8-y_2*y_7*y_8+y_3*y_7*y_8, y_4*y_5*y_6-y_4*y_5*y_8-y_4*y_6*y_8+y_5*y_6*y_8, y_1*y_2*y_4*y_6-y_1*y_2*y_4*y_7+y_1*y_2*y_6*y_7-y_1*y_4*y_6*y_7-y_2*y_4*y_6*y_7, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-4}, {-4}},{{y_8^2, y_7^2, y_6^2, y_5^2, y_4^2, y_3^2, y_1*y_3, y_2^2, y_1^2, y_2*y_3*y_7, y_4*y_5*y_6, y_1*y_2*y_5*y_7, y_1*y_2*y_4*y_6}})
G = graph {set {0, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 6}, set {1, 4}, set {1, 5}, set {1, 6}}
