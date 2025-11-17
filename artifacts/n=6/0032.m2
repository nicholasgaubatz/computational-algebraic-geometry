                                                                                                                                                                                                                                                2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y )}
                              3 4 7    3 4 8    3 7 8    4 7 8   2 4 6    2 4 8    2 6 8    4 6 8   2 3 6    2 3 7    2 6 7    3 6 7   1 4 5    1 4 8    1 5 8    4 5 8   1 3 5    1 3 7    1 5 7    3 5 7   1 2 5    1 2 6    1 5 6    2 5 6   1   2   3   4   5   6   7   8
                                2   2   2   2   2   2   2   2
          AOTinIdeal => ideal (y , y , y , y , y , y , y , y , y y y , y y y , y y y , y y y , y y y , y y y )
                                8   7   6   5   4   3   2   1   3 4 7   2 4 6   2 3 6   1 4 5   1 3 5   1 2 5
          graph => {set {0, 4}, set {1, 4}, set {2, 4}, set {3, 4}, set {0, 5}, set {1, 5}, set {2, 5}, set {3, 5}}
                                 2      3      4      5
          hSeries => 1 + 8T + 28T  + 50T  + 44T  + 15T
          hyperplanes => {a - e, b - e, c - e, d - e, a - f, b - f, c - f, d - f}
          numVariables => 8
          WLPfull => "A does not have WLP at A_3"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_8]
AOTideal = ideal map(R^1,R^{{-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_3*y_4*y_7-y_3*y_4*y_8-y_3*y_7*y_8+y_4*y_7*y_8, y_2*y_4*y_6-y_2*y_4*y_8-y_2*y_6*y_8+y_4*y_6*y_8, y_2*y_3*y_6-y_2*y_3*y_7-y_2*y_6*y_7+y_3*y_6*y_7, y_1*y_4*y_5-y_1*y_4*y_8-y_1*y_5*y_8+y_4*y_5*y_8, y_1*y_3*y_5-y_1*y_3*y_7-y_1*y_5*y_7+y_3*y_5*y_7, y_1*y_2*y_5-y_1*y_2*y_6-y_1*y_5*y_6+y_2*y_5*y_6, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}},{{y_8^2, y_7^2, y_6^2, y_5^2, y_4^2, y_3^2, y_2^2, y_1^2, y_3*y_4*y_7, y_2*y_4*y_6, y_2*y_3*y_6, y_1*y_4*y_5, y_1*y_3*y_5, y_1*y_2*y_5}})
G = graph {set {0, 4}, set {1, 4}, set {2, 4}, set {3, 4}, set {0, 5}, set {1, 5}, set {2, 5}, set {3, 5}}
