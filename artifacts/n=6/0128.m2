                                                                                                                                                                                                                                                                  2   2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y   - y y  , y y  - y y  - y y , y y  - y y  - y y , y y  - y y  - y y , y y y  - y y y   - y y y   + y y y  , y y y  - y y y   - y y y   + y y y  , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y , y  )}
                              6 8    6 10    8 10   6 7    6 9    7 9   1 3    1 5    3 5   1 2    1 4    2 4   4 5 9    4 5 10    4 9 10    5 9 10   2 3 9    2 3 10    2 9 10    3 9 10   4 5 7    4 5 8    4 7 8    5 7 8   2 3 7    2 3 8    2 7 8    3 7 8   1   2   3   4   5   6   7   8   9   10
                                2    2   2         2         2   2   2   2         2         2
          AOTinIdeal => ideal (y  , y , y , y y , y , y y , y , y , y , y , y y , y , y y , y , y y y , y y y , y y y , y y y , y y y , y y y )
                                10   9   8   6 8   7   6 7   6   5   4   3   1 3   2   1 2   1   7 8 9   4 5 9   2 3 9   4 5 7   2 3 7   2 3 4
          graph => {set {0, 2}, set {2, 4}, set {2, 5}, set {0, 4}, set {0, 5}, set {1, 3}, set {3, 4}, set {3, 5}, set {1, 4}, set {1, 5}}
                                  2      3      4      5
          hSeries => 1 + 10T + 41T  + 84T  + 84T  + 32T
          hyperplanes => {a - c, c - e, c - f, a - e, a - f, b - d, d - e, d - f, b - e, b - f}
          numVariables => 10
          WLPfull => "A does not have WLP at A_3"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_10]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_6*y_8-y_6*y_10-y_8*y_10, y_6*y_7-y_6*y_9-y_7*y_9, y_1*y_3-y_1*y_5-y_3*y_5, y_1*y_2-y_1*y_4-y_2*y_4, y_4*y_5*y_9-y_4*y_5*y_10-y_4*y_9*y_10+y_5*y_9*y_10, y_2*y_3*y_9-y_2*y_3*y_10-y_2*y_9*y_10+y_3*y_9*y_10, y_4*y_5*y_7-y_4*y_5*y_8-y_4*y_7*y_8+y_5*y_7*y_8, y_2*y_3*y_7-y_2*y_3*y_8-y_2*y_7*y_8+y_3*y_7*y_8, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}},{{y_10^2, y_9^2, y_8^2, y_6*y_8, y_7^2, y_6*y_7, y_6^2, y_5^2, y_4^2, y_3^2, y_1*y_3, y_2^2, y_1*y_2, y_1^2, y_7*y_8*y_9, y_4*y_5*y_9, y_2*y_3*y_9, y_4*y_5*y_7, y_2*y_3*y_7, y_2*y_3*y_4}})
G = graph {set {0, 2}, set {2, 4}, set {2, 5}, set {0, 4}, set {0, 5}, set {1, 3}, set {3, 4}, set {3, 5}, set {1, 4}, set {1, 5}}
