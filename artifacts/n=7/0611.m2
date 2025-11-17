                                                                                                                                                      2   2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y   - y y  , y y  - y y  - y y , y y  - y y  - y y , y y  - y y  - y y , y y y  - y y y   - y y y   + y y y  , y , y , y , y , y , y , y , y , y , y  )}
                              4 6    4 10    6 10   3 6    3 8    6 8   4 5    4 9    5 9   3 5    3 7    5 7   7 8 9    7 8 10    7 9 10    8 9 10   1   2   3   4   5   6   7   8   9   10
                                2    2   2   2   2               2               2   2   2   2
          AOTinIdeal => ideal (y  , y , y , y , y , y y , y y , y , y y , y y , y , y , y , y , y y y , y y y , y y y , y y y , y y y )
                                10   9   8   7   6   4 6   3 6   5   4 5   3 5   4   3   2   1   7 8 9   5 6 9   3 4 8   5 6 7   3 4 7
          graph => {set {0, 3}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 5}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}
                                  2      3       4      5      6
          hSeries => 1 + 10T + 41T  + 87T  + 100T  + 59T  + 14T
          hyperplanes => {a - d, a - g, b - e, c - e, e - f, e - g, b - f, b - g, c - f, c - g}
          numVariables => 10
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_10]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_4*y_6-y_4*y_10-y_6*y_10, y_3*y_6-y_3*y_8-y_6*y_8, y_4*y_5-y_4*y_9-y_5*y_9, y_3*y_5-y_3*y_7-y_5*y_7, y_7*y_8*y_9-y_7*y_8*y_10-y_7*y_9*y_10+y_8*y_9*y_10, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}},{{y_10^2, y_9^2, y_8^2, y_7^2, y_6^2, y_4*y_6, y_3*y_6, y_5^2, y_4*y_5, y_3*y_5, y_4^2, y_3^2, y_2^2, y_1^2, y_7*y_8*y_9, y_5*y_6*y_9, y_3*y_4*y_8, y_5*y_6*y_7, y_3*y_4*y_7}})
G = graph {set {0, 3}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 5}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}
