                                                                                                                                                                                                                                                                                                                                         2   2   2   2   2   2   2   2   2   2    2    2
HashTable{AOTideal => ideal (y y   - y y   + y  y  , y y  - y y   - y y  , y y  - y y  + y y , y y  - y y   + y y  , y y  - y y  - y y , y y y   + y y y   - y y  y   - y y  y  , y y y  - y y y   - y y y   + y y y  , y y y y  - y y y y   + y y y y   - y y y y   - y y y y  , y y y y  - y y y y  + y y y y  - y y y y  - y y y y , y , y , y , y , y , y , y , y , y , y  , y  , y  )}
                              9 10    9 12    10 12   6 8    6 10    8 10   4 5    4 8    5 8   2 3    2 12    3 12   1 3    1 5    3 5   7 8 11    7 8 12    7 11 12    8 11 12   6 7 9    6 7 11    6 9 11    7 9 11   1 2 4 7    1 2 4 11    1 2 7 11    1 4 7 11    2 4 7 11   1 2 4 6    1 2 4 9    1 2 6 9    1 4 6 9    2 4 6 9   1   2   3   4   5   6   7   8   9   10   11   12
                                2    2    2           2   2         2   2   2         2   2               2   2
          AOTinIdeal => ideal (y  , y  , y  , y y  , y , y , y y , y , y , y , y y , y , y , y y , y y , y , y , y y y  , y y y , y y y , y y y  y  , y y y y , y y y y , y y y y )
                                12   11   10   9 10   9   8   6 8   7   6   5   4 5   4   3   2 3   1 3   2   1   7 8 11   6 7 9   1 2 5   6 7 10 11   1 2 4 8   1 2 4 7   1 2 4 6
          graph => {set {0, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {5, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 12T + 61T  + 168T  + 262T  + 216T  + 72T
          hyperplanes => {a - d, d - f, d - g, a - e, a - g, b - e, c - e, e - g, b - f, b - g, c - f, f - g}
          numVariables => 12
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_4"


R = QQ[y_1..y_12]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-4}, {-4}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_9*y_10-y_9*y_12+y_10*y_12, y_6*y_8-y_6*y_10-y_8*y_10, y_4*y_5-y_4*y_8+y_5*y_8, y_2*y_3-y_2*y_12+y_3*y_12, y_1*y_3-y_1*y_5-y_3*y_5, y_7*y_8*y_11+y_7*y_8*y_12-y_7*y_11*y_12-y_8*y_11*y_12, y_6*y_7*y_9-y_6*y_7*y_11-y_6*y_9*y_11+y_7*y_9*y_11, y_1*y_2*y_4*y_7-y_1*y_2*y_4*y_11+y_1*y_2*y_7*y_11-y_1*y_4*y_7*y_11-y_2*y_4*y_7*y_11, y_1*y_2*y_4*y_6-y_1*y_2*y_4*y_9+y_1*y_2*y_6*y_9-y_1*y_4*y_6*y_9-y_2*y_4*y_6*y_9, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-4}, {-4}, {-4}, {-4}},{{y_12^2, y_11^2, y_10^2, y_9*y_10, y_9^2, y_8^2, y_6*y_8, y_7^2, y_6^2, y_5^2, y_4*y_5, y_4^2, y_3^2, y_2*y_3, y_1*y_3, y_2^2, y_1^2, y_7*y_8*y_11, y_6*y_7*y_9, y_1*y_2*y_5, y_6*y_7*y_10*y_11, y_1*y_2*y_4*y_8, y_1*y_2*y_4*y_7, y_1*y_2*y_4*y_6}})
G = graph {set {0, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {5, 6}}
