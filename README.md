# CarPark Management System
The CarPark Management System is a formal specification language-based project designed to streamline the management of parking spaces. It ensures robust operations with clear preconditions and postconditions. This system efficiently manages both reserved and non-reserved parking areas, tracks subscriptions, and handles various scenarios including weekdays and weekends. 

In urban settings, managing parking spaces can be challenging. The CarPark Management System simplifies this process by providing a structured approach to allocate, monitor, and maintain parking spaces in commercial establishments, residential complexes, and public facilities.

Key features of the system include:

- **Flexible Space Allocation**: Allows for the configuration of both reserved and non-reserved parking areas, accommodating different needs and user requirements.
  
- **Subscription Management**: Facilitates the management of subscriptions for reserved parking spaces, ensuring that allocated spots are efficiently utilised.

- **Dynamic Rules Handling**: Adjusts parking rules based on weekday and weekend scenarios, optimising space utilisation while maintaining operational flexibility.

- **User-friendly Interface**: Provides clear feedback and status updates, making it easy for administrators and users to understand current parking availability and occupancy.

- **Scalability and Customization**: Designed to be scalable for different sizes of car parks and customizable to adapt to specific operational requirements.

## What Does This Project Do?
The CarPark Management System allows users to efficiently manage parking spaces in a car park. It enables the allocation of parking spots to both reserved and non-reserved cars, manages subscriptions for reserved spaces, and adjusts parking rules based on whether it is a weekday or weekend. Key functionalities include:

- **Initialization of Car Park**: Set up the car park with specific capacities for reserved and non-reserved areas.
- **Availability Check**: Report the number of free non-reserved parking spaces.
- **Parking Management**: Allow cars to enter and exit the car park, with special handling for reserved spots.
- **Subscription Management**: Handle subscriptions for reserved parking spaces.
- **Weekend Operations**: Open reserved areas to all cars during weekends.
- **Car Park Closure**: Reset the car park at closing time, removing all parked cars.

## Class and Methods
### Class `CarPark`
#### Constants
- `MAX_CAPACITY`: Full capacity of the car park, including reserved and non-reserved areas.
- `MIN_FREE_SPACES`: Minimum number of spaces that must remain available in the non-reserved area.
- `reservedCapacity`: Maximum capacity of the reserved area.
- `nonReservedCapacity`: Maximum capacity of the non-reserved area.

#### Variables
- `isWeekend`: Tracks if it's currently a weekend.
- `reservedArea`: Set of reserved parking spaces.
- `nonReservedArea`: Set of non-reserved parking spaces.
- `subscription`: Set of cars with subscriptions.

#### Constructor
- `constructor(maxSize: nat, maxReserved: nat)`: Initialises the car park.

#### Methods

- `checkAvailability() returns(nat)`: Reports the number of non-reserved free spaces available.
- `enterCarPark(carID: nat) returns(bool)`: Allows a car without a reservation to enter the car park.
- `leaveCarPark(carID: nat) returns(bool)`: Allows a car to leave the car park.
- `enterReservedCarPark(carID: nat) returns(bool)`: Allows a car with a subscription to enter the reserved area.
- `makeSubscription(carID: nat) returns(bool)`: Registers a car for a reserved space.
- `openReservedArea() returns(bool)`: Removes parking restrictions on reserved spaces during weekends.
- `closeCarPark()`: Removes all parked cars and resets the car park.
- `PrintStarterPlan()`: Prints initial car park setup details.
- `PrintParkingPlan()`: Prints current car park status.

## Usage

### Example

```javascript
var fullCarParkCapacity := 13;
var reservedCarParkCapacity := 5;
var cp: CarPark := new CarPark(fullCarParkCapacity, reservedCarParkCapacity);

cp.PrintStarterPlan();
print("\n-----------------------------\n");

// Testing the enterCarPark()
print("\nTEST 1 \n");
var carID1 := cp.enterCarPark(5);
print("-carID1(5) has entered the Non-Reserved Area: ");
print(carID1);
cp.PrintParkingPlan();
print("\n-----------------------------\n");
```

## Testing
Various test scenarios have been implemented to ensure the proper functioning of the system. These include checking availability, handling car park entries and exits, managing subscriptions, and switching between weekday and weekend operations.
