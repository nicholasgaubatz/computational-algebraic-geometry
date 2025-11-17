                                                                                                                                                                                                                        2   2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y  - y y  + y y , y y y  - y y y   - y y y   + y y y  , y y y  - y y y   - y y y   + y y y  , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y , y  )}
                              5 6    5 8    6 8   2 4    2 6    4 6   7 8 9    7 8 10    7 9 10    8 9 10   3 4 9    3 4 10    3 9 10    4 9 10   3 4 7    3 4 8    3 7 8    4 7 8   2 3 5    2 3 7    2 5 7    3 5 7   1   2   3   4   5   6   7   8   9   10
                                2    2   2   2   2         2   2         2   2   2
          AOTinIdeal => ideal (y  , y , y , y , y , y y , y , y , y y , y , y , y , y y y , y y y , y y y , y y y , y y y y , y y y y )
                                10   9   8   7   6   5 6   5   4   2 4   3   2   1   7 8 9   3 4 9   3 4 7   2 3 5   2 3 6 9   2 3 6 7
          graph => {set {0, 3}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}
                                  2       3       4      5      6
          hSeries => 1 + 10T + 43T  + 100T  + 130T  + 88T  + 24T
          hyperplanes => {a - d, a - e, a - f, a - g, b - e, e - g, b - f, b - g, c - f, c - g}
          numVariables => 10
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_10]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_5*y_6-y_5*y_8-y_6*y_8, y_2*y_4-y_2*y_6+y_4*y_6, y_7*y_8*y_9-y_7*y_8*y_10-y_7*y_9*y_10+y_8*y_9*y_10, y_3*y_4*y_9-y_3*y_4*y_10-y_3*y_9*y_10+y_4*y_9*y_10, y_3*y_4*y_7-y_3*y_4*y_8-y_3*y_7*y_8+y_4*y_7*y_8, y_2*y_3*y_5-y_2*y_3*y_7-y_2*y_5*y_7+y_3*y_5*y_7, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-4}, {-4}},{{y_10^2, y_9^2, y_8^2, y_7^2, y_6^2, y_5*y_6, y_5^2, y_4^2, y_2*y_4, y_3^2, y_2^2, y_1^2, y_7*y_8*y_9, y_3*y_4*y_9, y_3*y_4*y_7, y_2*y_3*y_5, y_2*y_3*y_6*y_9, y_2*y_3*y_6*y_7}})
G = graph {set {0, 3}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}
