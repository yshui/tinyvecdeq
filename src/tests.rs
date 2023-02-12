/// Generate test cases that need internal access to fields
#[macro_export]
macro_rules! gen_tests_internal {
    ($vecdeq:tt) => {
        #[test]
        fn test_swap_front_back_remove() {
            fn test(back: bool) {
                // This test checks that every single combination of tail position and length is
                // tested. Capacity 15 should be large enough to cover every case.
                let mut tester = <$vecdeq<_>>::new([0; 15]);
                let usable_cap = tester.capacity();
                let final_len = usable_cap / 2;

                for len in 0..final_len {
                    let mut expected = <$vecdeq<_>>::new([0; 15]);
                    if back {
                        expected.extend(0..len)
                    } else {
                        expected.extend((0..len).rev())
                    };
                    for head_pos in 0..usable_cap {
                        tester.head = head_pos;
                        tester.len = 0;
                        if back {
                            for i in 0..len * 2 {
                                tester.push_front(i);
                            }
                            for i in 0..len {
                                assert_eq!(tester.swap_remove_back(i), Some(len * 2 - 1 - i));
                            }
                        } else {
                            for i in 0..len * 2 {
                                tester.push_back(i);
                            }
                            for i in 0..len {
                                let idx = tester.len() - 1 - i;
                                assert_eq!(tester.swap_remove_front(idx), Some(len * 2 - 1 - i));
                            }
                        }
                        assert!(tester.head <= tester.capacity());
                        assert!(tester.len <= tester.capacity());
                        assert_eq!(tester, expected);
                    }
                }
            }
            test(true);
            test(false);
        }

        #[test]
        fn test_insert() {
            // This test checks that every single combination of tail position, length, and
            // insertion position is tested. Capacity 15 should be large enough to cover
            // every case.

            let mut tester = <$vecdeq<_>>::new([0; 15]);
            // can't guarantee we got 15, so have to get what we got.
            // 15 would be great, but we will definitely get 2^k - 1, for k >= 4, or else
            // this test isn't covering what it wants to
            let cap = tester.capacity();

            // len is the length *after* insertion
            let minlen = if cfg!(miri) { cap - 1 } else { 1 }; // Miri is too slow
            for len in minlen..cap {
                // 0, 1, 2, .., len - 1
                let mut expected = <$vecdeq<_>>::new([0; 15]);
                expected.extend((0..).take(len));
                for head_pos in 0..cap {
                    for to_insert in 0..len {
                        tester.head = head_pos;
                        tester.len = 0;
                        for i in 0..len {
                            if i != to_insert {
                                tester.push_back(i);
                            }
                        }
                        tester.insert(to_insert, to_insert);
                        assert_eq!(tester, expected);
                    }
                }
            }
        }
        #[test]
        fn make_contiguous_big_head() {
            let mut tester = <$vecdeq<_>>::new([0; 15]);

            for i in 0..3 {
                tester.push_back(i);
            }

            for i in 3..10 {
                tester.push_front(i);
            }

            // 012......9876543
            assert_eq!(tester.capacity(), 15);
            assert_eq!(
                (&[9, 8, 7, 6, 5, 4, 3] as &[_], &[0, 1, 2] as &[_]),
                tester.as_slices()
            );

            tester.make_contiguous();
            assert_eq!(tester.head, 0);
            assert_eq!(
                (&[9, 8, 7, 6, 5, 4, 3, 0, 1, 2] as &[_], &[] as &[_]),
                tester.as_slices()
            );
            check_spare(&tester);
        }

        #[test]
        fn make_contiguous_big_tail() {
            let mut tester = <$vecdeq<_>>::new([0; 15]);

            for i in 0..8 {
                tester.push_back(i);
            }

            for i in 8..10 {
                tester.push_front(i);
            }

            // 01234567......98
            tester.make_contiguous();
            assert_eq!(tester.head, 0);
            assert_eq!(
                (&[9, 8, 0, 1, 2, 3, 4, 5, 6, 7] as &[_], &[] as &[_]),
                tester.as_slices()
            );
            check_spare(&tester);
        }

        #[test]
        fn make_contiguous_small_free() {
            let mut tester = <$vecdeq<_>>::new([0 as char; 16]);

            for i in b'A'..b'I' {
                tester.push_back(i as char);
            }

            for i in b'I'..b'N' {
                tester.push_front(i as char);
            }

            assert_eq!(tester, [
                'M', 'L', 'K', 'J', 'I', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H'
            ]);

            // ABCDEFGH...MLKJI
            tester.make_contiguous();
            assert_eq!(tester.head, 0);
            assert_eq!(
                (
                    &['M', 'L', 'K', 'J', 'I', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H'] as &[_],
                    &[] as &[_]
                ),
                tester.as_slices()
            );
            check_spare(&tester);

            tester.clear();
            for i in b'I'..b'N' {
                tester.push_back(i as char);
            }

            for i in b'A'..b'I' {
                tester.push_front(i as char);
            }

            // IJKLM...HGFEDCBA
            tester.make_contiguous();
            assert_eq!(tester.head, 0);
            assert_eq!(
                (
                    &['H', 'G', 'F', 'E', 'D', 'C', 'B', 'A', 'I', 'J', 'K', 'L', 'M'] as &[_],
                    &[] as &[_]
                ),
                tester.as_slices()
            );
            check_spare(&tester);
        }

        #[test]
        fn make_contiguous_head_to_end() {
            let mut tester = <$vecdeq<_>>::new([0 as char; 16]);

            for i in b'A'..b'L' {
                tester.push_back(i as char);
            }

            for i in b'L'..b'Q' {
                tester.push_front(i as char);
            }

            assert_eq!(tester, [
                'P', 'O', 'N', 'M', 'L', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K'
            ]);

            // ABCDEFGHIJKPONML
            tester.make_contiguous();
            assert_eq!(tester.head, 0);
            assert_eq!(
                (
                    &[
                        'P', 'O', 'N', 'M', 'L', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J',
                        'K'
                    ] as &[_],
                    &[] as &[_]
                ),
                tester.as_slices()
            );
            check_spare(&tester);

            tester.clear();
            for i in b'L'..b'Q' {
                tester.push_back(i as char);
            }

            for i in b'A'..b'L' {
                tester.push_front(i as char);
            }

            // LMNOPKJIHGFEDCBA
            tester.make_contiguous();
            assert_eq!(tester.head, 0);
            assert_eq!(
                (
                    &[
                        'K', 'J', 'I', 'H', 'G', 'F', 'E', 'D', 'C', 'B', 'A', 'L', 'M', 'N', 'O',
                        'P'
                    ] as &[_],
                    &[] as &[_]
                ),
                tester.as_slices()
            );
            check_spare(&tester);
        }

        #[test]
        fn test_remove() {
            // This test checks that every single combination of tail position, length, and
            // removal position is tested. Capacity 15 should be large enough to cover every
            // case.

            // can't guarantee we got 15, so have to get what we got.
            // 15 would be great, but we will definitely get 2^k - 1, for k >= 4, or else
            // this test isn't covering what it wants to
            const CAP: usize = 15;

            // len is the length *after* removal
            let minlen = if cfg!(miri) { CAP - 2 } else { 0 }; // Miri is too slow
            for len in minlen..CAP - 1 {
                // 0, 1, 2, .., len - 1
                let mut expected = <$vecdeq<_>>::new([0; 15]);
                expected.extend((0..).take(len));
                for head_pos in 0..CAP {
                    for to_remove in 0..=len {
                        let mut tester = <$vecdeq<_>>::new([0; CAP]);
                        tester.head = head_pos;
                        for i in 0..len {
                            if i == to_remove {
                                tester.push_back(1234);
                            }
                            tester.push_back(i);
                        }
                        if to_remove == len {
                            tester.push_back(1234);
                        }
                        tester.remove(to_remove);
                        assert!(tester.head <= tester.capacity());
                        assert!(tester.len <= tester.capacity());
                        assert_eq!(tester, expected);
                        check_spare(&tester);
                    }
                }
            }
        }
        #[test]
        fn test_range() {
            const CAP: usize = 7;
            let minlen = if cfg!(miri) { CAP - 1 } else { 0 }; // Miri is too slow
            for len in minlen..=CAP {
                for head in 0..CAP {
                    for start in 0..=len {
                        for end in start..=len {
                            let mut tester = <$vecdeq<_>>::new([0; CAP]);
                            tester.head = head;
                            for i in 0..len {
                                tester.push_back(i);
                            }

                            // Check that we iterate over the correct values
                            let range: Vec<_> = tester.range(start..end).copied().collect();
                            let expected: Vec<_> = (start..end).collect();
                            assert_eq!(range, expected);
                        }
                    }
                }
            }
        }

        #[test]
        fn test_range_mut() {
            const CAP: usize = 7;

            for len in 0..=CAP {
                for head in 0..CAP {
                    for start in 0..=len {
                        for end in start..=len {
                            let mut tester = <$vecdeq<_>>::new([0; CAP]);
                            tester.head = head;
                            for i in 0..len {
                                tester.push_back(i);
                            }

                            let head_was = tester.head;
                            let len_was = tester.len;

                            // Check that we iterate over the correct values
                            let range: Vec<_> = tester.range_mut(start..end).map(|v| *v).collect();
                            let expected: Vec<_> = (start..end).collect();
                            assert_eq!(range, expected);

                            // We shouldn't have changed the capacity or made the
                            // head or tail out of bounds
                            assert_eq!(tester.head, head_was);
                            assert_eq!(tester.len, len_was);
                        }
                    }
                }
            }
        }

        #[test]
        fn test_drain() {
            const CAP: usize = 7;

            for len in 0..=CAP {
                for head in 0..CAP {
                    for drain_start in 0..=len {
                        for drain_end in drain_start..=len {
                            let mut tester = <$vecdeq<_>>::new([0; CAP]);
                            tester.head = head;
                            tester.len = 0;
                            for i in 0..len {
                                tester.push_back(i);
                            }

                            // Check that we drain the correct values
                            let drained: Vec<_> = tester.drain(drain_start..drain_end).collect();
                            let drained_expected: Vec<_> = (drain_start..drain_end).collect();
                            assert_eq!(drained, drained_expected);

                            // We shouldn't have changed the capacity or made the
                            // head or tail out of bounds
                            assert!(tester.head <= tester.capacity());
                            assert!(tester.len <= tester.capacity());

                            // We should see the correct values in the VecDeque
                            let expected: Vec<_> = (0..drain_start).chain(drain_end..len).collect();
                            assert_eq!(tester, expected, "{drain_start:?} {drain_end:?}");
                            check_spare(&tester);
                        }
                    }
                }
            }
        }
    };
}

#[macro_export]
macro_rules! gen_tests {
    ($vecdeq:tt) => {
        #[test]
        fn test_get() {
            let mut tester = <$vecdeq<_>>::new([0; 5]);
            tester.push_back(1);
            tester.push_back(2);
            tester.push_back(3);

            assert_eq!(tester.len(), 3);

            assert_eq!(tester.get(1), Some(&2));
            assert_eq!(tester.get(2), Some(&3));
            assert_eq!(tester.get(0), Some(&1));
            assert_eq!(tester.get(3), None);

            tester.remove(0);

            assert_eq!(tester.len(), 2);
            assert_eq!(tester.get(0), Some(&2));
            assert_eq!(tester.get(1), Some(&3));
            assert_eq!(tester.get(2), None);
        }
        #[test]
        fn test_get_mut() {
            let mut tester = <$vecdeq<_>>::new([0; 3]);
            tester.push_back(1);
            tester.push_back(2);
            tester.push_back(3);

            assert_eq!(tester.len(), 3);

            if let Some(elem) = tester.get_mut(0) {
                assert_eq!(*elem, 1);
                *elem = 10;
            }

            if let Some(elem) = tester.get_mut(2) {
                assert_eq!(*elem, 3);
                *elem = 30;
            }

            assert_eq!(tester.get(0), Some(&10));
            assert_eq!(tester.get(2), Some(&30));
            assert_eq!(tester.get_mut(3), None);

            tester.remove(2);

            assert_eq!(tester.len(), 2);
            assert_eq!(tester.get(0), Some(&10));
            assert_eq!(tester.get(1), Some(&2));
            assert_eq!(tester.get(2), None);
        }

        #[test]
        fn test_swap() {
            let mut tester = <$vecdeq<_>>::new([0; 3]);
            tester.push_back(1);
            tester.push_back(2);
            tester.push_back(3);

            assert_eq!(tester, [1, 2, 3]);

            tester.swap(0, 0);
            assert_eq!(tester, [1, 2, 3]);
            tester.swap(0, 1);
            assert_eq!(tester, [2, 1, 3]);
            tester.swap(2, 1);
            assert_eq!(tester, [2, 3, 1]);
            tester.swap(1, 2);
            assert_eq!(tester, [2, 1, 3]);
            tester.swap(0, 2);
            assert_eq!(tester, [3, 1, 2]);
            tester.swap(2, 2);
            assert_eq!(tester, [3, 1, 2]);
        }
        #[test]
        fn test_clone_from() {
            let m = vec![1; 8];
            let n = vec![2; 12];
            let limit = if cfg!(miri) { 4 } else { 8 }; // Miri is too slow
            for pfv in 0..limit {
                for pfu in 0..limit {
                    for longer in 0..2 {
                        let (vr, ur) = if longer == 0 { (&m, &n) } else { (&n, &m) };
                        let mut v = <$vecdeq<_>>::new([0; 20]);
                        v.extend(vr.iter().copied());
                        for _ in 0..pfv {
                            v.push_front(1);
                        }
                        let mut u = <$vecdeq<_>>::new([0; 20]);
                        u.extend(ur.iter().copied());
                        for _ in 0..pfu {
                            u.push_front(2);
                        }
                        v.clone_from(&u);
                        assert_eq!(&v, &u);
                        check_spare(&v);
                        check_spare(&u);
                    }
                }
            }
        }

        #[test]
        fn make_contiguous_head_to_end_2() {
            // Another test case for #79808, taken from #80293.

            let mut dq = <$vecdeq<_>>::new([0; 16]);
            dq.extend(0..6);
            dq.pop_front();
            dq.pop_front();
            dq.push_back(6);
            dq.push_back(7);
            dq.push_back(8);
            dq.make_contiguous();
            let collected: Vec<_> = dq.iter().copied().collect();
            assert_eq!(dq.as_slices(), (&collected[..], &[] as &[_]));
            check_spare(&dq);
        }

        #[test]
        #[should_panic = "assertion failed: b < self.len"]
        fn test_swap_panic() {
            let mut tester = <$vecdeq<_>>::new([0; 3]);
            tester.push_back(1);
            tester.push_back(2);
            tester.push_back(3);
            tester.swap(2, 3);
        }
    };
}
