                                                                                                                                                                                                                                                                                                                                                                                                        2   2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y y  - y y y   - y y y   + y y y  , y y y  - y y y   - y y y   + y y y  , y y y  - y y y  - y y y  + y y y , y y y  - y y y   - y y y   + y y y  , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y   - y y y   + y y y  , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y , y  )}
                              4 5 9    4 5 10    4 9 10    5 9 10   3 5 8    3 5 10    3 8 10    5 8 10   3 4 8    3 4 9    3 8 9    4 8 9   2 5 7    2 5 10    2 7 10    5 7 10   2 4 7    2 4 9    2 7 9    4 7 9   2 3 7    2 3 8    2 7 8    3 7 8   1 5 6    1 5 10    1 6 10    5 6 10   1 4 6    1 4 9    1 6 9    4 6 9   1 3 6    1 3 8    1 6 8    3 6 8   1 2 6    1 2 7    1 6 7    2 6 7   1   2   3   4   5   6   7   8   9   10
                                2    2   2   2   2   2   2   2   2   2
          AOTinIdeal => ideal (y  , y , y , y , y , y , y , y , y , y , y y y , y y y , y y y , y y y , y y y , y y y , y y y , y y y , y y y , y y y )
                                10   9   8   7   6   5   4   3   2   1   4 5 9   3 5 8   3 4 8   2 5 7   2 4 7   2 3 7   1 5 6   1 4 6   1 3 6   1 2 6
          graph => {set {0, 5}, set {1, 5}, set {2, 5}, set {3, 5}, set {4, 5}, set {0, 6}, set {1, 6}, set {2, 6}, set {3, 6}, set {4, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 10T + 45T  + 110T  + 150T  + 107T  + 31T
          hyperplanes => {a - f, b - f, c - f, d - f, e - f, a - g, b - g, c - g, d - g, e - g}
          numVariables => 10
          WLPfull => "A does not have WLP at A_4"
          WLPin => "A does not have WLP at A_4"


R = QQ[y_1..y_10]
AOTideal = ideal map(R^1,R^{{-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_4*y_5*y_9-y_4*y_5*y_10-y_4*y_9*y_10+y_5*y_9*y_10, y_3*y_5*y_8-y_3*y_5*y_10-y_3*y_8*y_10+y_5*y_8*y_10, y_3*y_4*y_8-y_3*y_4*y_9-y_3*y_8*y_9+y_4*y_8*y_9, y_2*y_5*y_7-y_2*y_5*y_10-y_2*y_7*y_10+y_5*y_7*y_10, y_2*y_4*y_7-y_2*y_4*y_9-y_2*y_7*y_9+y_4*y_7*y_9, y_2*y_3*y_7-y_2*y_3*y_8-y_2*y_7*y_8+y_3*y_7*y_8, y_1*y_5*y_6-y_1*y_5*y_10-y_1*y_6*y_10+y_5*y_6*y_10, y_1*y_4*y_6-y_1*y_4*y_9-y_1*y_6*y_9+y_4*y_6*y_9, y_1*y_3*y_6-y_1*y_3*y_8-y_1*y_6*y_8+y_3*y_6*y_8, y_1*y_2*y_6-y_1*y_2*y_7-y_1*y_6*y_7+y_2*y_6*y_7, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}},{{y_10^2, y_9^2, y_8^2, y_7^2, y_6^2, y_5^2, y_4^2, y_3^2, y_2^2, y_1^2, y_4*y_5*y_9, y_3*y_5*y_8, y_3*y_4*y_8, y_2*y_5*y_7, y_2*y_4*y_7, y_2*y_3*y_7, y_1*y_5*y_6, y_1*y_4*y_6, y_1*y_3*y_6, y_1*y_2*y_6}})
G = graph {set {0, 5}, set {1, 5}, set {2, 5}, set {3, 5}, set {4, 5}, set {0, 6}, set {1, 6}, set {2, 6}, set {3, 6}, set {4, 6}}
