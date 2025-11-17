                                                                                                                                                                                                                                                                                                                                                         2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y )}
                              6 7 8    6 7 9    6 8 9    7 8 9   4 5 8    4 5 9    4 8 9    5 8 9   2 3 7    2 3 9    2 7 9    3 7 9   4 5 6    4 5 7    4 6 7    5 6 7   2 3 6    2 3 8    2 6 8    3 6 8   1 3 5    1 3 9    1 5 9    3 5 9   1 2 5    1 2 7    1 5 7    2 5 7   1 3 4    1 3 8    1 4 8    3 4 8   1 2 4    1 2 6    1 4 6    2 4 6   1   2   3   4   5   6   7   8   9
                                2   2   2   2   2   2   2   2   2
          AOTinIdeal => ideal (y , y , y , y , y , y , y , y , y , y y y , y y y , y y y , y y y , y y y , y y y , y y y , y y y , y y y )
                                9   8   7   6   5   4   3   2   1   6 7 8   4 5 8   2 3 7   4 5 6   2 3 6   1 3 5   1 2 5   1 3 4   1 2 4
          graph => {set {0, 4}, set {1, 4}, set {2, 4}, set {0, 5}, set {0, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}
                                 2      3      4      5
          hSeries => 1 + 9T + 36T  + 75T  + 78T  + 31T
          hyperplanes => {a - e, b - e, c - e, a - f, a - g, b - f, b - g, c - f, c - g}
          numVariables => 9
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_9]
AOTideal = ideal map(R^1,R^{{-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_6*y_7*y_8-y_6*y_7*y_9-y_6*y_8*y_9+y_7*y_8*y_9, y_4*y_5*y_8-y_4*y_5*y_9-y_4*y_8*y_9+y_5*y_8*y_9, y_2*y_3*y_7-y_2*y_3*y_9-y_2*y_7*y_9+y_3*y_7*y_9, y_4*y_5*y_6-y_4*y_5*y_7-y_4*y_6*y_7+y_5*y_6*y_7, y_2*y_3*y_6-y_2*y_3*y_8-y_2*y_6*y_8+y_3*y_6*y_8, y_1*y_3*y_5-y_1*y_3*y_9-y_1*y_5*y_9+y_3*y_5*y_9, y_1*y_2*y_5-y_1*y_2*y_7-y_1*y_5*y_7+y_2*y_5*y_7, y_1*y_3*y_4-y_1*y_3*y_8-y_1*y_4*y_8+y_3*y_4*y_8, y_1*y_2*y_4-y_1*y_2*y_6-y_1*y_4*y_6+y_2*y_4*y_6, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}},{{y_9^2, y_8^2, y_7^2, y_6^2, y_5^2, y_4^2, y_3^2, y_2^2, y_1^2, y_6*y_7*y_8, y_4*y_5*y_8, y_2*y_3*y_7, y_4*y_5*y_6, y_2*y_3*y_6, y_1*y_3*y_5, y_1*y_2*y_5, y_1*y_3*y_4, y_1*y_2*y_4}})
G = graph {set {0, 4}, set {1, 4}, set {2, 4}, set {0, 5}, set {0, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}
