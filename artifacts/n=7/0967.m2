                                                                                                                                                                                                                                                                                                                                        2   2   2   2   2   2   2   2   2   2    2    2
HashTable{AOTideal => ideal (y y   - y y   + y  y  , y y  - y y   + y y  , y y  - y y   - y y  , y y  - y y  - y y , y y  - y y  - y y , y y y   - y y y   + y y  y   - y y  y  , y y y   - y y y   + y y  y   - y y  y  , y y y y  - y y y y  - y y y y  + y y y y  - y y y y , y y y y  - y y y y  - y y y y  + y y y y  - y y y y , y , y , y , y , y , y , y , y , y , y  , y  , y  )}
                              9 10    9 11    10 11   7 8    7 12    8 12   6 8    6 10    8 10   1 3    1 5    3 5   1 2    1 4    2 4   4 5 11    4 5 12    4 11 12    5 11 12   2 3 11    2 3 12    2 11 12    3 11 12   4 5 6 7    4 5 6 9    4 5 7 9    4 6 7 9    5 6 7 9   2 3 6 7    2 3 6 9    2 3 7 9    2 6 7 9    3 6 7 9   1   2   3   4   5   6   7   8   9   10   11   12
                                2    2    2           2   2               2   2   2   2   2         2         2
          AOTinIdeal => ideal (y  , y  , y  , y y  , y , y , y y , y y , y , y , y , y , y , y y , y , y y , y , y y y  , y y y  , y y y  , y y y , y y y y  , y y y y , y y y y )
                                12   11   10   9 10   9   8   7 8   6 8   7   6   5   4   3   1 3   2   1 2   1   4 5 11   2 3 11   6 7 10   2 3 4   6 7 9 11   4 5 6 7   2 3 6 7
          graph => {set {0, 2}, set {2, 4}, set {2, 5}, set {0, 4}, set {0, 5}, set {1, 3}, set {3, 5}, set {3, 6}, set {1, 4}, set {1, 6}, set {4, 6}, set {5, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 12T + 61T  + 168T  + 262T  + 216T  + 72T
          hyperplanes => {a - c, c - e, c - f, a - e, a - f, b - d, d - f, d - g, b - e, b - g, e - g, f - g}
          numVariables => 12
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_4"


R = QQ[y_1..y_12]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-4}, {-4}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_9*y_10-y_9*y_11+y_10*y_11, y_7*y_8-y_7*y_12+y_8*y_12, y_6*y_8-y_6*y_10-y_8*y_10, y_1*y_3-y_1*y_5-y_3*y_5, y_1*y_2-y_1*y_4-y_2*y_4, y_4*y_5*y_11-y_4*y_5*y_12+y_4*y_11*y_12-y_5*y_11*y_12, y_2*y_3*y_11-y_2*y_3*y_12+y_2*y_11*y_12-y_3*y_11*y_12, y_4*y_5*y_6*y_7-y_4*y_5*y_6*y_9-y_4*y_5*y_7*y_9+y_4*y_6*y_7*y_9-y_5*y_6*y_7*y_9, y_2*y_3*y_6*y_7-y_2*y_3*y_6*y_9-y_2*y_3*y_7*y_9+y_2*y_6*y_7*y_9-y_3*y_6*y_7*y_9, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-4}, {-4}, {-4}},{{y_12^2, y_11^2, y_10^2, y_9*y_10, y_9^2, y_8^2, y_7*y_8, y_6*y_8, y_7^2, y_6^2, y_5^2, y_4^2, y_3^2, y_1*y_3, y_2^2, y_1*y_2, y_1^2, y_4*y_5*y_11, y_2*y_3*y_11, y_6*y_7*y_10, y_2*y_3*y_4, y_6*y_7*y_9*y_11, y_4*y_5*y_6*y_7, y_2*y_3*y_6*y_7}})
G = graph {set {0, 2}, set {2, 4}, set {2, 5}, set {0, 4}, set {0, 5}, set {1, 3}, set {3, 5}, set {3, 6}, set {1, 4}, set {1, 6}, set {4, 6}, set {5, 6}}
