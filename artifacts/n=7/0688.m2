                                                                                                                                                                                                                                                                                 2   2   2   2   2   2   2   2   2   2    2    2
HashTable{AOTideal => ideal (y  y   - y  y   + y  y  , y y  - y y   + y y  , y y  - y y   - y y  , y y  - y y  - y y , y y  - y y   + y y  , y y  - y y  + y y , y y y  - y y y   - y y y   + y y y  , y y y  - y y y   - y y y   + y y y  , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y , y  , y  , y  )}
                              10 11    10 12    11 12   8 9    8 12    9 12   6 7    6 11    7 11   5 7    5 9    7 9   3 4    3 12    4 12   2 4    2 7    4 7   5 6 8    5 6 10    5 8 10    6 8 10   2 3 6    2 3 10    2 6 10    3 6 10   2 3 5    2 3 8    2 5 8    3 5 8   1   2   3   4   5   6   7   8   9   10   11   12
                                2    2            2    2         2   2               2   2   2               2   2   2
          AOTinIdeal => ideal (y  , y  , y  y  , y  , y , y y , y , y , y y , y y , y , y , y , y y , y y , y , y , y , y y y , y y y , y y y , y y y , y y y )
                                12   11   10 11   10   9   8 9   8   7   6 7   5 7   6   5   4   3 4   2 4   3   2   1   5 6 9   5 6 8   2 3 7   2 3 6   2 3 5
          graph => {set {0, 3}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}, set {5, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 12T + 60T  + 157T  + 223T  + 161T  + 46T
          hyperplanes => {a - d, a - e, a - f, a - g, b - e, c - e, e - g, b - f, b - g, c - f, c - g, f - g}
          numVariables => 12
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_12]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_10*y_11-y_10*y_12+y_11*y_12, y_8*y_9-y_8*y_12+y_9*y_12, y_6*y_7-y_6*y_11-y_7*y_11, y_5*y_7-y_5*y_9-y_7*y_9, y_3*y_4-y_3*y_12+y_4*y_12, y_2*y_4-y_2*y_7+y_4*y_7, y_5*y_6*y_8-y_5*y_6*y_10-y_5*y_8*y_10+y_6*y_8*y_10, y_2*y_3*y_6-y_2*y_3*y_10-y_2*y_6*y_10+y_3*y_6*y_10, y_2*y_3*y_5-y_2*y_3*y_8-y_2*y_5*y_8+y_3*y_5*y_8, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}},{{y_12^2, y_11^2, y_10*y_11, y_10^2, y_9^2, y_8*y_9, y_8^2, y_7^2, y_6*y_7, y_5*y_7, y_6^2, y_5^2, y_4^2, y_3*y_4, y_2*y_4, y_3^2, y_2^2, y_1^2, y_5*y_6*y_9, y_5*y_6*y_8, y_2*y_3*y_7, y_2*y_3*y_6, y_2*y_3*y_5}})
G = graph {set {0, 3}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}, set {5, 6}}
