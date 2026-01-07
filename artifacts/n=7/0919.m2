                                                                                                                                                                                                          2   2   2   2   2   2   2   2   2   2    2    2
HashTable{AOTideal => ideal (y y   - y y   + y  y  , y y  - y y   + y y  , y y  - y y   - y y  , y y  - y y  - y y , y y  - y y   + y y  , y y  - y y   + y y  , y y  - y y  - y y , y y  - y y  - y y , y , y , y , y , y , y , y , y , y , y  , y  , y  )}
                              9 10    9 12    10 12   7 8    7 12    8 12   6 8    6 10    8 10   6 7    6 9    7 9   4 5    4 11    5 11   2 3    2 11    3 11   1 3    1 5    3 5   1 2    1 4    2 4   1   2   3   4   5   6   7   8   9   10   11   12
                                2    2    2           2   2               2         2   2         2   2               2         2
          AOTinIdeal => ideal (y  , y  , y  , y y  , y , y , y y , y y , y , y y , y , y , y y , y , y , y y , y y , y , y y , y )
                                12   11   10   9 10   9   8   7 8   6 8   7   6 7   6   5   4 5   4   3   2 3   1 3   2   1 2   1
          graph => {set {0, 2}, set {2, 4}, set {2, 6}, set {0, 4}, set {0, 6}, set {1, 3}, set {3, 5}, set {3, 6}, set {1, 5}, set {1, 6}, set {4, 6}, set {5, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 12T + 58T  + 144T  + 193T  + 132T  + 36T
          hyperplanes => {a - c, c - e, c - g, a - e, a - g, b - d, d - f, d - g, b - f, b - g, e - g, f - g}
          numVariables => 12
          WLPfull => "A does not have WLP at A_3"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_12]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_9*y_10-y_9*y_12+y_10*y_12, y_7*y_8-y_7*y_12+y_8*y_12, y_6*y_8-y_6*y_10-y_8*y_10, y_6*y_7-y_6*y_9-y_7*y_9, y_4*y_5-y_4*y_11+y_5*y_11, y_2*y_3-y_2*y_11+y_3*y_11, y_1*y_3-y_1*y_5-y_3*y_5, y_1*y_2-y_1*y_4-y_2*y_4, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_12^2, y_11^2, y_10^2, y_9*y_10, y_9^2, y_8^2, y_7*y_8, y_6*y_8, y_7^2, y_6*y_7, y_6^2, y_5^2, y_4*y_5, y_4^2, y_3^2, y_2*y_3, y_1*y_3, y_2^2, y_1*y_2, y_1^2}})
G = graph {set {0, 2}, set {2, 4}, set {2, 6}, set {0, 4}, set {0, 6}, set {1, 3}, set {3, 5}, set {3, 6}, set {1, 5}, set {1, 6}, set {4, 6}, set {5, 6}}
