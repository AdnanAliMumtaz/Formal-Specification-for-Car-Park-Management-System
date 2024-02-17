
class {:autocontracts} CarPark {

  const MAX_CAPACITY: nat
  const MIN_FREE_SPACES := 5
  const reservedCapacity: nat
  const nonReservedCapacity: nat
  var isWeekend: bool
  var reservedArea: set<nat>
  var nonReservedArea: set<nat>
  var subscription: set<nat>

  constructor(maxSize: nat, maxReserved: nat)
    requires maxSize - 5 >= maxReserved
    requires maxReserved > 0

    ensures isWeekend == false
    ensures reservedArea == nonReservedArea == {}
    ensures |subscription| == 0
    ensures MAX_CAPACITY == nonReservedCapacity + reservedCapacity
  {
    MAX_CAPACITY := maxSize;
    nonReservedCapacity := maxSize - maxReserved;
    reservedCapacity := maxReserved;
    isWeekend := false;
    reservedArea := {};
    nonReservedArea := {};
    subscription := {};
  }

  ghost predicate Valid()
  {
    // Rules that must be true throughtout the excution of the program
    MAX_CAPACITY == (nonReservedCapacity + reservedCapacity)
    &&
    MAX_CAPACITY >= (|nonReservedArea| + |reservedArea|)
    &&
    |nonReservedArea| <= nonReservedCapacity - MIN_FREE_SPACES // As long as the non-reserved area has the capacity
    &&
    |reservedArea| <= reservedCapacity
    &&
    |subscription| <= reservedCapacity
    &&

    // |reservedArea| <= |subscription|
    // &&
    nonReservedArea * reservedArea == {} // The same Car must not be in non-reserved or reserved at the same time
    &&
    nonReservedArea * subscription == {} // The car must is the nonreservedArea must not be in the subscription
    // &&
    // (reservedArea \ subscription == {} )
    // !(isWeekend && (reservedArea \ subscription != {}))

  }

  // To report on the number of non-reserved free spaces currently available
  method checkAvailability() returns(availablity: nat)

    modifies this

    // Cases
    ensures !isWeekend ==> (availablity == (nonReservedCapacity - |nonReservedArea|))
    ensures isWeekend ==> (availablity == (MAX_CAPACITY - (|nonReservedArea| + |reservedArea|)))

    // Preservation of Other State Properties
    ensures isWeekend == old(isWeekend)
    ensures nonReservedArea == old(nonReservedArea)
    ensures reservedArea == old(reservedArea)
    ensures subscription == old(subscription)
  {
    if (isWeekend)
    {
      availablity := MAX_CAPACITY - (|nonReservedArea| + |reservedArea|);
    }
    else {
      availablity := nonReservedCapacity - |nonReservedArea|;
    }
  }

  // To allow any car without a reservation to enter the car park
  method enterCarPark(carID: nat) returns(success: bool)

    modifies this

    // Good Cases
    ensures carID !in old(subscription) && carID !in old(nonReservedArea) && (carID !in old(reservedArea))  && (old(|nonReservedArea|) < (nonReservedCapacity - 5)) ==> success
    ensures success ==> nonReservedArea == old(nonReservedArea) + {carID}

    // Bad Cases
    ensures carID in old(nonReservedArea) ==> !success
    ensures carID in old(reservedArea) ==> !success
    ensures carID in old(subscription) ==> !success
    ensures old(|nonReservedArea|) >= (nonReservedCapacity - 5) ==> !success
    ensures !success ==> nonReservedArea == old(nonReservedArea)

    // Preservation of Other State Properties
    ensures isWeekend == old(isWeekend)
    ensures reservedArea == old(reservedArea)
    ensures subscription == old(subscription)
  {
    if ( carID !in nonReservedArea && carID !in reservedArea && carID !in subscription && (|nonReservedArea| < (nonReservedCapacity - 5)))
    {
      nonReservedArea := nonReservedArea + {carID};
      success := true;
    }
    else {
      success := false;
    }
  }

  // To allow any car from any area to leave the car park
  method leaveCarPark(carID: nat) returns(left: bool)
    modifies this

    // Good Cases
    ensures carID in old(nonReservedArea) ==> left && nonReservedArea == old(nonReservedArea) - {carID}
    ensures carID in old(reservedArea) ==> left && reservedArea == old(reservedArea) - {carID}

    // Bad Casses - nonReserved/reserved
    ensures carID !in old(nonReservedArea) && carID !in old(reservedArea) ==> !left
    ensures !left ==> nonReservedArea == old(nonReservedArea)
    ensures !left ==> reservedArea == old(reservedArea)

    // Preservation of Other State Properties
    ensures isWeekend == old(isWeekend)
    ensures subscription == old(subscription)
  {
    if (carID in nonReservedArea)
    {
      nonReservedArea := nonReservedArea - {carID};
      left := true;
    }
    else if (carID in reservedArea) {
      reservedArea := reservedArea - {carID};
      left := true;
    }
    else {
      left := false;
    }
  }

  // To allow a car with a subscription to enter the car park’s reserved area on a weekday, or to enter the car park generally on a weekend day.
  method enterReservedCarPark(carID: nat) returns (entered: bool)
    modifies this

    // Good Cases
    ensures !isWeekend && carID !in old(nonReservedArea) && carID !in old(reservedArea) && carID in old(subscription) && (old(|reservedArea|)  < reservedCapacity) ==> entered
    ensures isWeekend && carID !in old(nonReservedArea) && carID !in old(reservedArea) && old(|reservedArea|) < reservedCapacity  ==> entered
    ensures entered ==> reservedArea == old(reservedArea) + {carID}

    // Bad Cases
    ensures carID in old(nonReservedArea) ==> !entered
    ensures carID in old(reservedArea) ==> !entered
    ensures !isWeekend && carID !in old(subscription) ==> !entered
    ensures old(|reservedArea|) >= reservedCapacity ==> !entered
    ensures !entered ==> reservedArea == old(reservedArea)

    // Preservation of Other State Properties
    ensures isWeekend == old(isWeekend)
    ensures nonReservedArea == old(nonReservedArea)
    ensures subscription == old(subscription)
  {
    if (!isWeekend && carID in subscription && carID !in reservedArea && carID !in nonReservedArea && |reservedArea| < reservedCapacity)
    {
      reservedArea := reservedArea + {carID};
      entered := true;
    }
    else if (isWeekend && carID !in reservedArea && carID !in nonReservedArea && |reservedArea| < reservedCapacity)
    {
      reservedArea := reservedArea + {carID};
      entered := true;
    }
    else {
      entered := false;
    }
  }

  // // Logic to allow a car to be registered as having a reserved space when the owner pays the subscription
  method makeSubscription(carID: nat) returns(registered: bool)
    // requires |subscription| < |reservedArea|
    modifies this

    // Good Cases
    ensures carID !in old(subscription) && carID !in old(nonReservedArea) && carID !in old(reservedArea) && old(|subscription|) < reservedCapacity ==> registered
    ensures registered ==> subscription == old(subscription) + {carID}

    // Bad Cases
    ensures carID in old(subscription) ==> !registered
    ensures carID in old(nonReservedArea) ==> !registered
    ensures carID in old(reservedArea) ==> !registered
    ensures old(|subscription|) >= reservedCapacity ==> !registered
    ensures !registered ==> subscription == old(subscription)

    // Preservation of Other State Properties
    ensures isWeekend == old(isWeekend)
    ensures nonReservedArea == old(nonReservedArea)
    ensures reservedArea == old(reservedArea)
  {
    if ( carID !in subscription && carID !in nonReservedArea && carID !in reservedArea && |subscription| < reservedCapacity)
    {
      subscription := subscription + {carID};
      registered := true;
    }
    else{
      registered := false;
    }
  }

  // To remove parking restrictions on the reserved spaces (at the weekend).
  method openReservedArea() returns (open: bool)
    modifies this

    // Good Cases
    ensures old(isWeekend) == false ==> open
    ensures open ==> isWeekend == true

    //Bad Cases
    ensures old(isWeekend) == true ==> !open
    ensures !open ==> old(isWeekend) == isWeekend

    // Preservation of Other State Properties
    ensures nonReservedArea == old(nonReservedArea)
    ensures reservedArea == old(reservedArea)
    ensures subscription == old(subscription)
  {
    if (isWeekend == false)
    {
      isWeekend := true;
      open := true;
    }
    else {
      open := false;
    }
  }

  // To remove and crush remaining parked cars at closing time
  method closeCarPark()
    modifies this

    // Good Cases
    ensures nonReservedArea == {}
    ensures reservedArea == {}
    ensures isWeekend == false

    // Preservation of Other State Properties
    ensures subscription == old(subscription)
  {
    nonReservedArea := {};
    reservedArea := {};
    isWeekend := false;
  }

  method PrintBasicPlan()
  {
    print("\nCarPark Max Capacity: ");
    print(MAX_CAPACITY);
    print("\n");
    print("Non Reserved Max Capacity: ");
    print(nonReservedCapacity);
    print("\n");
    print("Reserved Max Capacity: ");
    print(reservedCapacity);
    print("\n-----------------------------");
  }

  method PrintParkingPlan()
  {
    // var nonReservedSpace := checkAvailability();
    print("Current CarPark Status");
    print("\n>Non-Reserved Area: ");
    print(nonReservedArea);
    // print("   Spaces Left[");
    // print(nonReservedSpace);
    // print("]");
    print("\n");
    print(">Reserved Area: ");
    print(reservedArea);
    print("\n");
    print(">Current Subscriptions: ");
    print(subscription);
    // print("\n");
  }
}

method Main()
{
  // NOTE: PLEASE UNCOMMENT EACH FUNCTION TESTCASES, OTHERWISE VSCODE CAN timeout
  var fullCarParkCapacity := 13;
  var reservedCarParkCapacity := 5;
  var cp: CarPark := new CarPark( fullCarParkCapacity, reservedCarParkCapacity);

  print("====================================\n");
  print("               CarPark              \n");
  print("====================================");
  cp.PrintBasicPlan();

  ////////////// Testing the enterCarPark()
  ////// Testing if the car can enter the non-reserved area
  print("\nTEST 1 \n");
  var carID1 := cp.enterCarPark(5);
  print("-carID1(5) has entered the Non-Reserved Area: ");
  print(carID1);
  print("\n-----------------------------\n");


  ////// Testing if the same car can enter the carpark twice
  print("TEST 2 \n");
  var carID1Duplicate := cp.enterCarPark(5);
  print("-carID1(5) has entered the Non-Reserved Area: ");
  print(carID1Duplicate);
  print(" (fails as the same car tries to enter again)");
  print("\n-----------------------------\n");

  ////// Testing if the non-reserved are is deemed to be full when 5 spaces are left
  print("TEST 3 \n");
  var carID2 := cp.enterCarPark(12);
  var carID3 := cp.enterCarPark(19);
  var carID4 := cp.enterCarPark(21);
  print("-carID2(12) has entered the Non-Reserved Area: ");
  print(carID2);
  print("\n");
  print("-carID3(19) has entered the Non-Reserved Area: ");
  print(carID3);
  print("\n");
  print("-carID4(21) has entered the Non-Reserved Area: ");
  print(carID4);
  print(" (fails because only 5 spaces are left in the non-reserved area)");
  // print("\n");
  print("\n-----------------------------\n");

  ////// Testing if the car with subscription can enter the non-reserved carpark -- CONFIRMED
  print("TEST 4\n");
  //Making two cars leave to make a space in the carpark
  var carID3Leaving := cp.leaveCarPark(19);
  var carID4Leaving := cp.leaveCarPark(19);

  // Making a subscription for the car
  var carID5Subscription := cp.makeSubscription(9);
  print("-carID5(9) has registered as having a reserved space: ");
  print(carID5Subscription);
  print("\n");

  var carID5 := cp.enterCarPark(9);
  print("-carID5(9) has entered the Non-Reserved Area: ");
  print(carID5);
  print(" (fails to enter because it has a subscription-reserved Space)");
  print("\n-----------------------------\n");

  cp.PrintParkingPlan();
  print("\n-----------------------------\n");




  ////////////// Testing the leaveCarPark()
  ////// Testing if a car not parked in the park can leave
  print("TEST 5\n");
  var carID5Left := cp.leaveCarPark(9);
  print("-carID5(9) has left the carPark: ");
  print(carID5Left);
  print(" (fails to leave as their is no carID5(9) car in the carpark)");
  print("\n");
  print("\n-----------------------------\n");

  ////// Testing if a car parked in a non-reserved area can leave
  print("TEST 6\n");
  var carID2Left := cp.leaveCarPark(12);
  print("-carID2(12) has left the carpark(Non-Reserved Area): ");
  print(carID2Left);
  print("\n-----------------------------\n");

  ////// Testing if a car parked in a reserved area can leave
  print("TEST 7\n");
  var carID6 := cp.enterReservedCarPark(9);
  print("-carID6(9) has entered the Non-Reserved Area: ");
  print(carID6);
  print("\n-----------------------------\n");

  ////////////// Testing the checkAvailability() 
  ////// Testing if the availability status is correct on Weekday -- MAYNEEDSOMEWORK
  print("TEST 8\n");
  var nonReservedAvailability := cp.checkAvailability();
  print("Current Non-Reserved Area Availability (on Weekday): ");
  print(nonReservedAvailability);
  print("\n-----------------------------\n");

  ////////////// Testing the makeSubscription()
  ////// Testing if it can make a subscription twice for the same car
  print("TEST 9\n");
  var carID6Subscription := cp.makeSubscription(9);
  print("-carID6(9) has registered as having a reserved space: ");
  print(carID6Subscription);
  print(" (fails to make a subscription, because it already has a subscription)");
  print("\n-----------------------------\n");

  ////// Testing if it can make a subscription for car already parked in non-reserved area -- CONFIRMED
  print("TEST 10\n");
  var carID1Subscription := cp.makeSubscription(5);
  print("-carID1(5) has registered as having a reserved space: ");
  print(carID1Subscription);
  print(" (fails to make a subscription, because it is already parked in Non-Reserved Area)");
  print("\n-----------------------------\n");




  ////////////// Testing the enterReservedCarPark()
  ////// Testing if car without a subscription can enter the reserved area.
  print("TEST 11\n");
  var carID7 := cp.enterReservedCarPark(231);
  print("-carID7(231) has entered the Reserved Area: ");
  print(carID7);
  print(" (fails to enter because doesn't have subscription)");
  print("\n-----------------------------\n");

  ////// Testing if car is already parked in a reserved can enter again
  print("TEST 12\n");
  var carID8 := cp.enterReservedCarPark(9);
  var carID8Duplicate := cp.enterReservedCarPark(9);
  print("-carID8(9) has entered the Reserved Area: ");
  print(carID8Duplicate);
  print(" (fails because same car can't enter again)");
  print("\n-----------------------------\n");

  ////// Testing if a car without the subscription can enter the reserved area on weekend -- NEEDSOMEWORK
  print("TEST 13\n");
  var isReservedOpen := cp.openReservedArea();
  var carID9 := cp.enterReservedCarPark(98);
  print("-carID9(98) has entered the Reserved Area: ");
  print(carID9);
  print(" (enters without making a subscription, because it is a Weekend!)");
  print("\n-----------------------------\n");

  ////////////// Testing the openReservedArea()
  ////// Testing if it can open reserved area if it already opened -- NEEDSOMEWORK
  print("TEST 14\n");
  var alreadyOpened := cp.openReservedArea();
  print("Reserved Area is opened: ");
  print(alreadyOpened);
  print(" (fails to open, because it is already opened)");
  print("\n-----------------------------\n");


  ////////////// Testing the closeCarPark()
  ////// Testing if all the cars are removed when the function is called
  print("TEST 15\n");
  cp.closeCarPark();
  print("The carPark has been closed!");
  cp.PrintParkingPlan();
  print("\n-----------------------------\n");
}
